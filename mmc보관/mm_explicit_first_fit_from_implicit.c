/*
 * mm_explicit_first_fit_from_implicit.c
 *
 * Converted from mm_implicit_first_fit.c into an explicit free-list allocator.
 * - Free blocks are kept in a doubly linked explicit list (LIFO insertion).
 * - Allocation policy is first-fit over the explicit free list.
 * - Realloc policy is simple malloc-copy-free.
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

/* Basic block constants. */
#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   (1 << 12)

/* Explicit-list related sizes. */
#define OVERHEAD    (2 * WSIZE)
#define ALIGNMENT   8
#define PTRSIZE     ((size_t)sizeof(void *))

/* Utilities. */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define MINBLOCKSIZE ((size_t)ALIGN(OVERHEAD + 2 * PTRSIZE))

/* Header/footer packing. */
#define PACK(size, alloc) ((unsigned int)((size) | (alloc)))
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Block pointer helpers (bp = payload pointer). */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Explicit free-list pointers stored in free-block payload. */
#define NEXT_FREEP(bp) (*(char **)(bp))
#define PREV_FREEP(bp) (*(char **)((char *)(bp) + PTRSIZE))

/* Heap and free-list heads. */
static char *heap_listp = NULL;
static char *free_listp = NULL;

/* Internal helpers. */
static size_t adjust_block_size(size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * adjust_block_size - Convert requested payload size to aligned internal block size.
 */
static size_t adjust_block_size(size_t size)
{
    if (size <= DSIZE) {
        return 2 * DSIZE;
    }
    return ALIGN(size + OVERHEAD);
}

/*
 * mm_init - Initialize heap skeleton and create initial free chunk.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(heap_listp, 0);                         /* alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* epilogue header */

    heap_listp += (2 * WSIZE);
    free_listp = NULL;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * insert_free_block - Insert free block at free-list head (LIFO).
 */
static void insert_free_block(void *bp)
{
    NEXT_FREEP(bp) = free_listp;
    PREV_FREEP(bp) = NULL;

    if (free_listp != NULL) {
        PREV_FREEP(free_listp) = bp;
    }
    free_listp = bp;
}

/*
 * remove_free_block - Remove a free block from explicit list in O(1).
 */
static void remove_free_block(void *bp)
{
    if (PREV_FREEP(bp) != NULL) {
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    } else {
        free_listp = NEXT_FREEP(bp);
    }

    if (NEXT_FREEP(bp) != NULL) {
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    }
}

/*
 * coalesce - Merge with free neighbors and reinsert merged block into free list.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_free_block(bp);
        return bp;
    }

    if (prev_alloc && !next_alloc) {
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_free_block(bp);
        return bp;
    }

    if (!prev_alloc && next_alloc) {
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_free_block(bp);
        return bp;
    }

    remove_free_block(PREV_BLKP(bp));
    remove_free_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    insert_free_block(bp);
    return bp;
}

/*
 * extend_heap - Extend heap and return coalesced free block.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if (size < MINBLOCKSIZE) {
        size = MINBLOCKSIZE;
    }

    if ((bp = mem_sbrk((int)size)) == (void *)-1) {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * find_fit - First-fit search over explicit free list.
 */
static void *find_fit(size_t asize)
{
    char *bp;

    for (bp = free_listp; bp != NULL; bp = NEXT_FREEP(bp)) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
    }
    return NULL;
}

/*
 * place - Allocate from free block bp. Split if remainder is usable.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remain = csize - asize;

    remove_free_block(bp);

    if (remain >= MINBLOCKSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remain, 0));
        PUT(FTRP(bp), PACK(remain, 0));

        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate payload bytes.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    asize = adjust_block_size(size);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }

    place(bp, asize);
    return bp;
}

/*
 * mm_free - Free a block and coalesce.
 */
void mm_free(void *ptr)
{
    size_t size;

    if (ptr == NULL) {
        return;
    }

    size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Simple malloc-copy-free policy.
 */
void *mm_realloc(void *ptr, size_t size)
{
    char *newptr;
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

    oldsize = GET_SIZE(HDRP(ptr));
    copySize = oldsize - OVERHEAD;
    if (size < copySize) {
        copySize = size;
    }

    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
