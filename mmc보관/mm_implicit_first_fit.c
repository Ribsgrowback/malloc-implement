/*
 * mm_implicit_first_fit.c
 *
 * Implicit free list allocator using first-fit policy.
 *
 * Key characteristics:
 * 1) Implicit free list:
 *    - There is no separate free-list pointer structure.
 *    - We linearly scan all heap blocks to find a free fit.
 * 2) Boundary tags:
 *    - Each block has header/footer with (size | alloc bit).
 *    - This enables O(1) neighbor checks for coalescing.
 * 3) Placement:
 *    - First fit policy (first free block that is large enough).
 *    - Split block if remainder is large enough for a valid block.
 * 4) Realloc:
 *    - Simple malloc-copy-free fallback implementation.
 */

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

/* Basic block size constants. */
#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   (1 << 12)

/* Utility macro. */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack block size and allocation bit into one word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Raw read/write a word at address p. */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Extract size / alloc from packed header/footer word. */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Convert payload pointer to block metadata pointers. */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Move to physically adjacent blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Points to prologue payload area after initialization. */
static char *heap_listp = NULL;

/* Internal helper prototypes. */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize heap with:
 * [alignment padding | prologue block | epilogue header]
 * then extend once to create an initial free block.
 */
int mm_init(void)
{
    /* Create initial empty heap skeleton (4 words). */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }

    /* Alignment padding. */
    PUT(heap_listp, 0);
    /* Prologue header/footer (allocated, size 8). */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    /* Initial epilogue header (allocated, size 0). */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    /* heap_listp points to prologue payload. */
    heap_listp += (2 * WSIZE);

    /* Create first free chunk so allocator can serve requests. */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * extend_heap - grow heap by words and return coalesced free block.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Keep block aligned to double word by forcing even word count. */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk((int)size)) == (void *)-1) {
        return NULL;
    }

    /* Initialize the new free block. */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    /* Move epilogue header to the end of new heap. */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* Merge with previous tail block if it was free. */
    return coalesce(bp);
}

/*
 * coalesce - merge adjacent free blocks if possible.
 *
 * Cases:
 * 1) prev alloc, next alloc: no merge
 * 2) prev alloc, next free : merge with next
 * 3) prev free,  next alloc: merge with prev
 * 4) prev free,  next free : merge all three
 */
static void *coalesce(void *bp)
{
    /* Allocation status of neighbor blocks. */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /* Current block size before merge. */
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: nothing to merge. */
    if (prev_alloc && next_alloc) {
        return bp;
    /* Case 2: merge with next block. */
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    /* Case 3: merge with previous block. */
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    /* Case 4: merge previous + current + next. */
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * find_fit - first-fit search over implicit heap blocks.
 */
static void *find_fit(size_t asize)
{
    char *bp;

    /* Start from first real block and scan until epilogue (size 0). */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        /* First free block that can hold asize wins. */
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

/*
 * place - allocate asize bytes from free block bp.
 * Split block when remainder can hold at least minimal block (2*DSIZE).
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    /* Split if remainder is big enough. */
    if ((csize - asize) >= (2 * DSIZE)) {
        /* Front part becomes allocated block. */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        /* Tail part remains free block. */
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        /* Otherwise consume the whole free block. */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - allocate at least size bytes of payload.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    /* By convention we return NULL for zero-size request. */
    if (size == 0) {
        return NULL;
    }

    /* Compute adjusted block size including overhead and alignment. */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    /* Try to find a reusable free block first. */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found: grow heap and place. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }

    place(bp, asize);
    return bp;
}

/*
 * mm_free - free a block and coalesce.
 */
void mm_free(void *ptr)
{
    size_t size;

    /* free(NULL) is a no-op. */
    if (ptr == NULL) {
        return;
    }

    /* Mark block free in both header and footer. */
    size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    /* Attempt immediate neighbor merge. */
    coalesce(ptr);
}

/*
 * mm_realloc - simple realloc using malloc-copy-free.
 *
 * Semantics:
 * - ptr == NULL -> mm_malloc(size)
 * - size == 0   -> mm_free(ptr), return NULL
 * - otherwise:
 *   allocate new block, copy min(old_payload, new_size), free old block
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t oldsize;
    size_t copySize;

    if (ptr == NULL) {
        return mm_malloc(size);
    }

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }

    /* oldsize includes header/footer, so payload = oldsize - DSIZE. */
    oldsize = GET_SIZE(HDRP(ptr));
    copySize = oldsize - DSIZE;
    if (size < copySize) {
        copySize = size;
    }

    /* Preserve prefix data and release old block. */
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
