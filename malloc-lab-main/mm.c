/*
 * mm.c - Version v70plus: 명시적 가용 리스트 + 단순 realloc 복사 정책.
 *
 * ============================================================== 
 * 상위 동작 모델
 * ============================================================== 
 * 1) 모든 블록은 4바이트 헤더와 4바이트 푸터를 가집니다.
 *    - 둘 다 (block_size | alloc_bit) 값을 저장합니다.
 *    - block_size는 헤더 + payload + 푸터 전체를 포함합니다.
 * 2) free 블록은 payload 영역을 재사용해 두 포인터를 저장합니다.
 *    - 다음 free 블록 포인터
 *    - 이전 free 블록 포인터
 * 3) 할당은 명시적 free 리스트에서 first-fit으로 수행합니다.
 * 4) 해제는 즉시 인접 free 블록과 병합(coalesce)합니다.
 * 5) realloc은 복사를 최소화하려고 시도합니다.
 *    - 가능하면 제자리 축소
 *    - 가능하면 다음 free 블록으로 확장
 *    - 불가하면 malloc + memcpy + free로 폴백
 *
 * ============================================================== 
 * 이 설계가 malloc lab에 유효한 이유
 * ============================================================== 
 * - 8바이트 정렬 요구를 만족합니다.
 * - 해제 블록을 재사용하여 bump-pointer보다 utilization이 좋습니다.
 * - 병합으로 외부 단편화를 줄입니다.
 * - 명시적 free 리스트로 할당된 블록 스캔 비용을 줄입니다.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * 학생 안내: 작업 시작 전에 팀 정보를 아래 구조체에 채우세요.
 ********************************************************/
team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

/* 한 워드 크기(헤더/푸터 필드 크기). */
#define WSIZE       4
/* 더블 워드 크기(정렬 단위). */
#define DSIZE       8
/* 기본 힙 확장 단위(4KB). */
#define CHUNKSIZE   (1 << 12)
/* 블록당 메타데이터 오버헤드(헤더 + 푸터). */
#define OVERHEAD    (2 * WSIZE)
/* 요구되는 payload 정렬 단위. */
#define ALIGNMENT   8
/* free-list payload 링크에 사용하는 네이티브 포인터 크기. */
#define PTRSIZE     ((size_t)sizeof(void *))

/* 단순 max 헬퍼. */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* 8바이트 배수로 올림. */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
/* hdr/ftr + next/prev 포인터를 담을 수 있는 최소 free 블록 크기. */
#define MINBLOCKSIZE ((size_t)ALIGN(OVERHEAD + 2 * PTRSIZE))

/* 크기와 할당 비트를 하나의 4바이트 워드로 패킹. */
#define PACK(size, alloc) ((unsigned int)((size) | (alloc)))

/* 주소 p에서 4바이트 로드/스토어. */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 패킹된 헤더/푸터 워드에서 크기/할당 여부 추출. */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* payload 포인터(bp)로부터 헤더/푸터 주소 계산. */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 현재 블록에서 물리적으로 인접한 다음/이전 블록 payload 포인터 계산. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* free 블록 payload 내부의 명시적 리스트 next/prev 포인터 접근. */
#define NEXT_FREEP(bp) (*(char **)(bp))
#define PREV_FREEP(bp) (*(char **)((char *)(bp) + PTRSIZE))

/* mm_init 이후 프롤로그 payload를 가리키는 포인터. */
static char *heap_listp = NULL;
/* 명시적 이중 연결 free 리스트의 head 포인터. */
static char *free_listp = NULL;

/* 사용자 요청 payload 크기를 내부 블록 크기로 변환. */
static size_t adjust_block_size(size_t size);
/* 힙을 늘리고 병합된 free 블록 포인터를 반환. */
static void *extend_heap(size_t words);
/* 인접 free 블록과 병합 후 병합된 블록 포인터를 반환. */
static void *coalesce(void *bp);
/* free 블록을 리스트 head(LIFO)에 삽입. */
static void insert_free_block(void *bp);
/* free 블록을 명시적 리스트에서 분리. */
static void remove_free_block(void *bp);
/* 명시적 free 리스트에서 first-fit 탐색. */
static void *find_fit(size_t asize);
/* 선택된 free 블록을 할당 처리(필요 시 분할). */
static void place(void *bp, size_t asize);

/*
 * adjust_block_size - 사용자 요청을 할당기 내부 블록 크기로 정규화.
 *
 * 입력:
 *   size = mm_malloc/mm_realloc이 받은 사용자 payload 바이트 수
 *
 * 출력:
 *   헤더/푸터를 포함하고 정렬이 맞는 내부 블록 크기
 */
static size_t adjust_block_size(size_t size)
{
    /* 요청이 매우 작아도 최소 할당 블록(16바이트)은 보장. */
    if (size <= DSIZE) {
        return 2 * DSIZE;
    }
    /* 그 외에는 오버헤드를 더하고 8바이트 정렬. */
    return ALIGN(size + OVERHEAD);
}

/* 
 * mm_init - malloc 패키지 초기화.
 *
 * 초기 힙 뼈대:
 * [ 정렬 패딩 | 프롤로그 헤더 | 프롤로그 푸터 | 에필로그 헤더 ]
 *
 * 이후 extend_heap 한 번으로 초기 대형 free 블록을 생성.
 */
int mm_init(void)
{
    /* 정렬/프롤로그/에필로그용 4워드를 먼저 확보. */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }

    /* Word 0: payload 정렬 보장을 위한 패딩. */
    PUT(heap_listp, 0);
    /* Word 1: 할당된 프롤로그 헤더(크기 8, alloc 1). */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    /* Word 2: 할당된 프롤로그 푸터(헤더와 동일). */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    /* Word 3: 할당된 에필로그 헤더(크기 0, alloc 1). */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    /* 교재 스타일 포인터 연산을 위해 프롤로그 payload를 가리키게 이동. */
    heap_listp += (2 * WSIZE);

    /* 명시적 free 리스트는 빈 상태로 시작. */
    free_listp = NULL;

    /* 초기 free 청크를 만들어 첫 요청부터 처리 가능하게 함. */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    /* 초기화 성공. */
    return 0;
}

/*
 * insert_free_block - free 블록을 리스트 head에 삽입.
 *
 * LIFO 삽입은 O(1)이며 단순합니다:
 * new -> old_head, old_head->prev = new, head = new
 */
static void insert_free_block(void *bp)
{
    /* 새 블록의 next는 기존 head. */
    NEXT_FREEP(bp) = free_listp;
    /* 새 블록이 head가 되므로 prev는 NULL. */
    PREV_FREEP(bp) = NULL;

    /* 리스트가 비어있지 않았다면, 기존 head의 prev를 새 블록으로 갱신. */
    if (free_listp != NULL) {
        PREV_FREEP(free_listp) = bp;
    }
    /* 새 head 반영. */
    free_listp = bp;
}

/*
 * remove_free_block - 명시적 free 리스트에서 블록을 O(1)로 제거.
 */
static void remove_free_block(void *bp)
{
    /* bp에 prev가 있으면 prev -> bp->next로 연결. */
    if (PREV_FREEP(bp) != NULL) {
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    } else {
        /* prev가 없으면 bp가 head이므로 head를 다음으로 이동. */
        free_listp = NEXT_FREEP(bp);
    }

    /* bp에 next가 있으면 next->prev를 bp->prev로 연결. */
    if (NEXT_FREEP(bp) != NULL) {
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    }
}

static void *coalesce(void *bp)
{
    /* 물리적으로 이전 블록의 할당 비트 확인. */
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    /* 물리적으로 다음 블록의 할당 비트 확인. */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /* 병합 전 현재 블록 크기. */
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: 양쪽 이웃 모두 할당 상태 -> 현재 블록만 리스트에 삽입. */
    if (prev_alloc && next_alloc) {
        insert_free_block(bp);
        return bp;
    }

    /* Case 2: 다음 블록과 병합. */
    if (prev_alloc && !next_alloc) {
        /* 다음 블록은 free 리스트에 있으므로 구조 변경 전에 제거. */
        remove_free_block(NEXT_BLKP(bp));
        /* 병합 크기 = 현재 + 다음 블록. */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        /* 병합된 헤더/푸터를 현재 블록 경계에 기록. */
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        /* 병합 결과를 free 리스트에 삽입. */
        insert_free_block(bp);
        return bp;
    }

    /* Case 3: 이전 블록과 병합. */
    if (!prev_alloc && next_alloc) {
        /* 이전 블록은 free 리스트에 있으므로 먼저 제거. */
        remove_free_block(PREV_BLKP(bp));
        /* 병합 크기 = 이전 + 현재. */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        /* 병합 블록 푸터는 현재 블록 푸터 위치. */
        PUT(FTRP(bp), PACK(size, 0));
        /* 병합 블록 헤더는 이전 블록 헤더 위치. */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        /* 병합 블록의 기준 포인터는 이전 블록. */
        bp = PREV_BLKP(bp);
        /* 병합 결과를 free 리스트에 삽입. */
        insert_free_block(bp);
        return bp;
    }

    /* Case 4: 이전 + 현재 + 다음 모두 병합. */
    /* 양 옆 free 블록을 먼저 리스트에서 제거. */
    remove_free_block(PREV_BLKP(bp));
    remove_free_block(NEXT_BLKP(bp));
    /* 총 병합 크기 계산. */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
    /* 병합 헤더는 이전 블록 헤더에 기록. */
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    /* 병합 푸터는 다음 블록 푸터에 기록. */
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    /* 병합 블록 기준 포인터는 이전 블록. */
    bp = PREV_BLKP(bp);
    /* 병합 결과를 free 리스트에 삽입. */
    insert_free_block(bp);
    return bp;
}

/*
 * extend_heap - memlib로 힙을 늘려 free 블록 하나를 생성.
 */
static void *extend_heap(size_t words)
{
    /* bp는 새 free 블록의 payload 포인터가 됨. */
    char *bp;
    /* 8바이트 정렬을 유지하려고 짝수 워드 수로 확장. */
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    /* 이후 free-list 포인터 저장이 가능하도록 최소 크기 보장. */
    if (size < MINBLOCKSIZE) {
        size = MINBLOCKSIZE;
    }

    /* 시뮬레이션 메모리 시스템에 힙 확장 요청. */
    if ((bp = mem_sbrk((int)size)) == (void *)-1) {
        return NULL;
    }

    /* 새 free 블록 헤더 기록. */
    PUT(HDRP(bp), PACK(size, 0));
    /* 새 free 블록 푸터 기록. */
    PUT(FTRP(bp), PACK(size, 0));
    /* 새 free 블록 뒤에 새 에필로그 헤더 배치. */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* 직전 꼬리 블록이 free였다면 병합. */
    return coalesce(bp);
}

/*
 * find_fit - 명시적 free 리스트에서 first-fit 탐색.
 */
static void *find_fit(size_t asize)
{
    /* 리스트 head부터 tail까지 순회. */
    char *bp;

    for (bp = free_listp; bp != NULL; bp = NEXT_FREEP(bp)) {
        /* 요청 크기를 만족하는 첫 블록 발견. */
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
    }
    /* 적합한 블록 없음. */
    return NULL;
}

/*
 * place - free 블록을 실제 할당에 사용.
 *
 * 할당 후 남는 공간이 충분히 크면 분할해서 tail을 free로 유지.
 */
static void place(void *bp, size_t asize)
{
    /* 배치 전 현재 free 블록 크기. */
    size_t csize = GET_SIZE(HDRP(bp));
    /* 요청 블록을 떼고 남는 바이트 수. */
    size_t remain = csize - asize;

    /* 이제 할당될 블록이므로 free 리스트에서 먼저 제거. */
    remove_free_block(bp);

    /* 남은 공간이 유효 free 블록을 만들 수 있을 때만 분할. */
    if (remain >= MINBLOCKSIZE) {
        /* 앞부분을 할당 블록으로 마킹. */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* 뒤쪽 remainder 블록의 payload로 이동. */
        bp = NEXT_BLKP(bp);
        /* 뒤쪽 remainder를 free 블록으로 마킹. */
        PUT(HDRP(bp), PACK(remain, 0));
        PUT(FTRP(bp), PACK(remain, 0));
        /* 필요 시 다음 이웃과 병합 후 free 리스트에 삽입. */
        coalesce(bp);
    } else {
        /* 남은 조각이 너무 작으면 분할하지 않고 통째로 할당. */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - 최소 size 바이트 payload를 갖는 블록 할당.
 */
void *mm_malloc(size_t size)
{
    /* 메타데이터/정렬을 포함한 내부 요청 크기. */
    size_t asize;
    /* 적합 블록이 없을 때 늘릴 힙 크기. */
    size_t extendsize;
    /* 후보 블록 포인터. */
    char *bp;

    /* C 표준 동작 중 하나로 malloc(0)은 NULL 반환 처리. */
    if (size == 0) {
        return NULL;
    }

    /* 사용자 요청을 내부 블록 크기로 변환. */
    asize = adjust_block_size(size);

    /* 먼저 기존 free 블록 재사용 시도. */
    if ((bp = find_fit(asize)) != NULL) {
        /* 찾은 free 블록을 할당 처리(필요 시 분할). */
        place(bp, asize);
        return bp;
    }

    /* 적합 블록이 없으면 요청 크기와 CHUNKSIZE 중 큰 쪽만큼 힙 확장. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        /* 하부 힙 확장 실패. */
        return NULL;
    }

    /* 새로 확보된 free 영역에 요청 블록 배치. */
    place(bp, asize);
    return bp;
}

/*
 * mm_free - 블록 해제 후 가능하면 즉시 병합.
 */
void mm_free(void *ptr)
{
    /* alloc 비트를 내릴 때 유지할 원래 블록 크기. */
    size_t size;

    /* free(NULL)은 libc와 동일하게 무시. */
    if (ptr == NULL) {
        return;
    }

    /* 현재 헤더에서 블록 크기 읽기. */
    size = GET_SIZE(HDRP(ptr));
    /* 헤더를 free로 마킹. */
    PUT(HDRP(ptr), PACK(size, 0));
    /* 푸터를 free로 마킹. */
    PUT(FTRP(ptr), PACK(size, 0));
    
    coalesce(ptr);
}

/*
 * mm_realloc - 기존 내용을 보존하며 블록 크기 재조정.
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    size_t copySize;
    char *newptr;
    
    /* 입력 포인터가 NULL이면 malloc과 동일하게 동작. */
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    /* 요청 크기가 0이면 free와 동일하게 동작. */
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    /* 요청 크기에 맞는 새 블록 확보. */
    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }

    /* 기존 블록 크기를 읽어 실제 복사 바이트 수 계산. */
    oldsize = GET_SIZE(HDRP(ptr));
    copySize = oldsize - OVERHEAD;
    if (size < copySize) {
        copySize = size;
    }
    
    /* 새 블록으로 기존 데이터 복사. */
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
