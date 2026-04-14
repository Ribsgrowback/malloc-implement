/*
 * mm_explicit_first_fit_from_implicit.c
 *
 * mm_implicit_first_fit.c를 명시적 가용 리스트 할당기로 변환한 버전.
 * - free 블록은 이중 연결 명시적 리스트(LIFO 삽입)로 관리한다.
 * - 할당 정책은 명시적 free 리스트에 대한 first-fit이다.
 * - realloc 정책은 기본 malloc-copy-free 방식이다.
 */

//mm_malloc -> find_fit/extend_heap -> place

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

/* 기본 블록 상수 */
#define WSIZE       4                   /* 워드 크기(헤더/푸터 크기): 4바이트 */
#define DSIZE       8                   /* 더블 워드 크기/정렬 단위 기준: 8바이트 */
#define CHUNKSIZE   (1 << 12)           /* 힙을 한 번 확장할 기본 크기: 4096바이트 */

/* 명시적 리스트 관련 크기 */
#define OVERHEAD    (2 * WSIZE)         /* 헤더+푸터 오버헤드 */
#define ALIGNMENT   8                   /* 정렬 단위 */
#define PTRSIZE     ((size_t)sizeof(void *)) /* 포인터 저장 크기 */

/* 유틸리티 */
#define MAX(x, y) ((x) > (y) ? (x) : (y)) /* 두 값 중 큰 값 반환 */

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) /* 8바이트 경계로 올림 */
#define MINBLOCKSIZE ((size_t)ALIGN(OVERHEAD + 2 * PTRSIZE)) /* free 블록 최소 크기 */

/* 헤더/푸터 비트 패킹 */
#define PACK(size, alloc) ((unsigned int)((size) | (alloc))) /* size와 할당 비트 합치기 */
#define GET(p)      (*(unsigned int *)(p)) /* p 위치 4바이트 읽기 */
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* p 위치 4바이트 쓰기 */
#define GET_SIZE(p)  (GET(p) & ~0x7) /* 하위 3비트 제거하여 블록 크기 얻기 */
#define GET_ALLOC(p) (GET(p) & 0x1) /* 하위 1비트로 할당 상태 얻기 */

/* 블록 포인터 헬퍼 (bp = payload 포인터) */
#define HDRP(bp) ((char *)(bp) - WSIZE) /* payload에서 헤더 주소 계산 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* payload에서 푸터 주소 계산 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) /* 다음 블록 payload 주소 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) /* 이전 블록 payload 주소 */

/* free 블록 payload에 저장되는 명시적 리스트 포인터 */
#define NEXT_FREEP(bp) (*(char **)(bp)) /* 현재 free 블록의 next 포인터 슬롯 */
#define PREV_FREEP(bp) (*(char **)((char *)(bp) + PTRSIZE)) /* 현재 free 블록의 prev 포인터 슬롯 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) /* realloc 복사용 size_t 정렬 크기 */

/* 힙/가용 리스트 헤드 */
static char *heap_listp = NULL;
static char *free_listp = NULL;

/* 내부 헬퍼 함수 선언 */
static size_t adjust_block_size(size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * adjust_block_size - 요청 payload 크기를 내부 정렬 블록 크기로 변환한다.
 */
static size_t adjust_block_size(size_t size)
{
    if (size <= DSIZE) {                 /* 아주 작은 요청은 최소 할당 블록으로 처리 */
        return 2 * DSIZE;                /* 최소 할당 블록 크기(헤더/푸터 포함 16B) 반환 */
    }
    return ALIGN(size + OVERHEAD);       /* payload+오버헤드를 8바이트 경계로 정렬 */
}

/*
 * mm_init - 책에 있는거 그대로임
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) { /* 패딩/프롤로그/에필로그 공간 요청 */
        return -1;                                          /* 힙 초기화 실패 */
    }

    PUT(heap_listp, 0);                             /* 정렬 패딩 워드 기록 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더(할당 상태) 기록 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 푸터(할당 상태) 기록 */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* 에필로그 헤더(크기 0, 할당) 기록 */

    heap_listp = heap_listp + (2 * WSIZE);                     /* heap_listp를 프롤로그 payload로 이동 */
    free_listp = NULL;                             /* free 리스트를 빈 상태로 초기화 */

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {  /* 초기 가용 블록을 위해 힙 확장 */
        return -1;                                 /* 확장 실패 시 초기화 실패 */
    }
    return 0; 
}

/*
 * insert_free_block - free 블록을 free 리스트 머리에(LIFO) 삽입한다.
 */
static void insert_free_block(void *bp)
{
    NEXT_FREEP(bp) = free_listp;                   /* 새 블록의 next를 기존 head로 연결 */
    PREV_FREEP(bp) = NULL;                         /* 새 블록은 새 head이므로 prev는 NULL */

    if (free_listp != NULL) {                      /* 기존 head가 있으면 */
        PREV_FREEP(free_listp) = bp;               /* 기존 head의 prev를 새 블록으로 연결 */
    }
    free_listp = bp;                               /* free 리스트 head 갱신 */
}

/*
 * remove_free_block - 명시적 리스트에서 free 블록을 O(1)로 제거한다.
 */
static void remove_free_block(void *bp)
{
    if (PREV_FREEP(bp) != NULL) {                  /* 이전 노드가 있으면 */
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp); /* 이전 노드의 next를 현재의 next로 변경 */
    } else {                                       /* 현재 노드가 head면 */
        free_listp = NEXT_FREEP(bp);               /* head를 다음 노드로 이동 */
    }

    if (NEXT_FREEP(bp) != NULL) {                  /* 다음 노드가 있으면 */
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp); /* 다음 노드의 prev를 현재의 prev로 변경 */
    }
}

/*
 * coalesce - 인접 free 블록과 병합하고 병합 결과를 free 리스트에 다시 삽입한다.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); /* 이전 블록 할당 상태 읽기 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); /* 다음 블록 할당 상태 읽기 */
    size_t size = GET_SIZE(HDRP(bp));                   /* 현재 블록 크기 읽기 */

    if (prev_alloc && next_alloc) {                 /* 양옆이 모두 할당 상태인 경우 */
        insert_free_block(bp);                      /* 현재 블록만 free 리스트에 삽입 */
        return bp;                                  /* 현재 블록 반환 */
    }

    if (prev_alloc && !next_alloc) {                /* 다음 블록만 free인 경우 */
        remove_free_block(NEXT_BLKP(bp));           /* 다음 free 블록을 리스트에서 제거 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      /* 현재+다음 크기 합산 */
        PUT(HDRP(bp), PACK(size, 0));               /* 병합 블록 헤더 갱신 */
        PUT(FTRP(bp), PACK(size, 0));               /* 병합 블록 푸터 갱신 */
        insert_free_block(bp);                      /* 병합된 블록 삽입 */
        return bp;                                  /* 병합된 현재 위치 반환 */
    }

    if (!prev_alloc && next_alloc) {                /* 이전 블록만 free인 경우 */
        remove_free_block(PREV_BLKP(bp));           /* 이전 free 블록을 리스트에서 제거 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      /* 이전+현재 크기 합산 */
        PUT(FTRP(bp), PACK(size, 0));               /* 병합 블록 푸터 갱신 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    /* 병합 블록 헤더 갱신 */
        bp = PREV_BLKP(bp);                         /* bp를 병합 시작 블록(이전)으로 이동 */
        insert_free_block(bp);                      /* 병합된 블록 삽입 */
        return bp;                                  /* 병합된 블록 반환 */
    }

    remove_free_block(PREV_BLKP(bp));               /* 이전 free 블록 제거 */
    remove_free_block(NEXT_BLKP(bp));               /* 다음 free 블록 제거 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))); /* 세 블록 크기 합산 */
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));        /* 병합 블록 헤더를 이전 위치에 기록 */
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));        /* 병합 블록 푸터를 다음 위치 끝에 기록 */
    bp = PREV_BLKP(bp);                             /* bp를 병합 시작 위치로 이동 */
    insert_free_block(bp);                          /* 병합된 블록 삽입 */
    return bp;                                      /* 병합된 블록 반환 */
}

/*
 * extend_heap - 힙을 확장하고 병합된 free 블록을 반환한다.
 */
static void *extend_heap(size_t words)
{
    char *bp;                                               /* 새 free 블록 payload 포인터 */
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; /* 짝수 워드로 맞춰 정렬 유지 */

    if (size < MINBLOCKSIZE) {                              /* 최소 블록보다 작으면 */
        size = MINBLOCKSIZE;                                /* 최소 free 블록 크기로 보정 */
    }

    if ((bp = mem_sbrk((int)size)) == (void *)-1) {         /* 힙 끝을 size만큼 확장 */
        return NULL;                                        /* 확장 실패 */
    }

    PUT(HDRP(bp), PACK(size, 0));                           /* 새 free 블록 헤더 기록 */
    PUT(FTRP(bp), PACK(size, 0));                           /* 새 free 블록 푸터 기록 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                   /* 새 에필로그 헤더 기록 */

    return coalesce(bp);                                    /* 인접 free와 병합 후 반환 */
}

/*
 * find_fit - 명시적 free 리스트에서 first-fit 탐색을 수행한다.
 */
static void *find_fit(size_t asize)
{
    char *bp;                                           /* free 리스트 순회 포인터 */

    for (bp = free_listp; bp != NULL; bp = NEXT_FREEP(bp)) { /* head부터 끝까지 순회 */
        if (GET_SIZE(HDRP(bp)) >= asize) {                  /* 요청 크기를 만족하면 */
            return bp;                                      /* 해당 블록 즉시 반환 */
        }
    }
    return NULL;                                            /* 적합 블록 없음 */
}


```mermaid
flowchart TD
    A["mm_init"] --> B["extend_heap"]
    B --> C["coalesce"]
    C --> D["insert_free_block"]

    E["mm_malloc(size)"] --> F{"size == 0?"}
    F -- Yes --> G["return NULL"]
    F -- No --> H["adjust_block_size"]
    H --> I["find_fit (explicit list first-fit)"]
    I --> J{"fit found?"}
    J -- Yes --> K["place"]
    J -- No --> L["extend_heap"]
    L --> M["coalesce"]
    M --> K
    K --> N["return bp"]

    O["mm_free(ptr)"] --> P{"ptr == NULL?"}
    P -- Yes --> Q["return"]
    P -- No --> R["mark free header/footer"]
    R --> S["coalesce"]
    S --> D

    T["mm_realloc(ptr,size)"] --> U{"ptr==NULL?"}
    U -- Yes --> E
    U -- No --> V{"size==0?"}
    V -- Yes --> O
    V -- No --> W["newptr = mm_malloc(size)"]
    W --> X{"newptr==NULL?"}
    X -- Yes --> Y["return NULL"]
    X -- No --> Z["memcpy min(old,size)"]
    Z --> AA["mm_free(oldptr)"]
    AA --> AB["return newptr"]

```


/*
 * place - free 블록 bp에서 할당한다. 남는 공간이 충분하면 분할한다.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));                  /* 선택된 free 블록의 현재 크기 */
    size_t remain = csize - asize;                      /* 할당 후 남는 크기 */

    remove_free_block(bp);                              /* 할당 대상 블록을 free 리스트에서 제거 */

    if (remain >= MINBLOCKSIZE) {                       /* 남는 공간이 유효 free 블록이면 분할 */
        PUT(HDRP(bp), PACK(asize, 1));                  /* 앞부분을 할당 블록 헤더로 기록 */
        PUT(FTRP(bp), PACK(asize, 1));                  /* 앞부분을 할당 블록 푸터로 기록 */

        bp = NEXT_BLKP(bp);                             /* 뒷부분(잔여 블록)으로 이동 */
        PUT(HDRP(bp), PACK(remain, 0));                 /* 잔여 free 블록 헤더 기록 */
        PUT(FTRP(bp), PACK(remain, 0));                 /* 잔여 free 블록 푸터 기록 */

        coalesce(bp);                                   /* 잔여 블록을 필요 시 주변 free와 병합 */
    } else {
        PUT(HDRP(bp), PACK(csize, 1));                  /* 분할 없이 전체 블록을 할당 처리 */
        PUT(FTRP(bp), PACK(csize, 1));                  /* 분할 없이 전체 블록 푸터 갱신 */
    }
}

/*
 * mm_malloc - payload 바이트를 할당한다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;                                       /* 정렬/오버헤드 반영 내부 요청 크기 */
    size_t extendsize;                                  /* 적합 블록이 없을 때 확장 크기 */
    char *bp;                                           /* 할당 대상 블록 포인터 */

    if (size == 0) {                                    /* 0바이트 요청은 */
        return NULL;                                    /* NULL 반환 */
    }

    asize = adjust_block_size(size);                    /* 내부 블록 크기로 보정 */

    if ((bp = find_fit(asize)) != NULL) {               /* free 리스트에서 적합 블록 탐색 */
        place(bp, asize);                               /* 해당 블록에 배치 */
        return bp;                                      /* payload 포인터 반환 */
    }

    extendsize = MAX(asize, CHUNKSIZE);                 /* 요청 또는 기본 청크 중 큰 값으로 확장 */
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) { /* 힙 확장 시도 */
        return NULL;                                    /* 확장 실패면 할당 실패 */
    }

    place(bp, asize);                                   /* 확장으로 얻은 블록에 배치 */
    return bp;                                          /* payload 포인터 반환 */
}

/*
 * mm_free - 블록을 free 처리하고 인접 free 블록과 병합한다.
 */
void mm_free(void *ptr)
{
    size_t size;                                        /* 반환할 블록 크기 */

    if (ptr == NULL) {                                  /* NULL free는 no-op */
        return;                                         /* 즉시 반환 */
    }

    size = GET_SIZE(HDRP(ptr));                         /* 현재 블록 크기 조회 */
    PUT(HDRP(ptr), PACK(size, 0));                      /* 헤더를 free 상태로 표시 */
    PUT(FTRP(ptr), PACK(size, 0));                      /* 푸터를 free 상태로 표시 */
    coalesce(ptr);                                      /* 인접 free 블록과 즉시 병합 */
}

/*
 * mm_realloc - 새 블록을 할당하고 데이터를 복사한 뒤 기존 블록을 해제한다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;                                 /* 기존 블록 포인터 저장 */
    void *newptr;                                       /* 새 블록 포인터 */
    size_t copySize;                                    /* 복사할 바이트 수 */

    newptr = mm_malloc(size);                           /* 새 크기로 먼저 할당 시도 */
    if (newptr == NULL)                                 /* 할당 실패하면 */
        return NULL;                                    /* 실패 반환 */
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE); /* 기존 블록에서 복사 가능 크기 읽기 */
    if (size < copySize)                                /* 요청 크기가 더 작으면 */
        copySize = size;                                /* 요청 크기만큼만 복사 */
    memcpy(newptr, oldptr, copySize);                   /* 기존 데이터 새 블록으로 복사 */
    mm_free(oldptr);                                    /* 기존 블록 반납 */
    return newptr;                                      /* 새 블록 반환 */
}
