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

/* Size of one word (header/footer field size). */
#define WSIZE       4
/* Size of one double word (alignment unit). */
#define DSIZE       8
/* Default heap growth chunk (4KB). */
#define CHUNKSIZE   (1 << 12)
    /* Header + footer bytes per block. */
    #define OVERHEAD    (2 * WSIZE)
    /* Required payload alignment. */
    #define ALIGNMENT   8
    /* Native pointer size used in free-list payload links. */
    #define PTRSIZE     ((size_t)sizeof(void *))

/* Simple max helper. */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* Round up to nearest multiple of 8. */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
/* Smallest free block that can store hdr/ftr + next/prev pointers. */
#define MINBLOCKSIZE ((size_t)ALIGN(OVERHEAD + 2 * PTRSIZE))

/* Pack size and allocation bit into one 4-byte word. */
#define PACK(size, alloc) ((unsigned int)((size) | (alloc)))

/* Raw 4-byte load/store helpers at address p. */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Extract size/allocation status from packed header/footer word. */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Convert payload pointer (bp) to header/footer pointer. */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Move from one block payload pointer to adjacent block payload pointer. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Read/write explicit free-list next/prev pointers inside free block payload. */
#define NEXT_FREEP(bp) (*(char **)(bp))
#define PREV_FREEP(bp) (*(char **)((char *)(bp) + PTRSIZE))

/* Pointer to prologue payload (after mm_init). */
static char *heap_listp = NULL;
/* Head pointer of explicit doubly linked free list. */
static char *free_listp = NULL;

/* Convert requested payload size to aligned internal block size. */
static size_t adjust_block_size(size_t size);
/* Grow heap and return coalesced free block pointer. */
static void *extend_heap(size_t words);
/* Merge with neighboring free blocks and return merged block. */
static void *coalesce(void *bp);
/* Push free block to free-list head (LIFO policy). */
static void insert_free_block(void *bp);
/* Detach free block from explicit free list. */
static void remove_free_block(void *bp);
/* First-fit search over explicit free list. */
static void *find_fit(size_t asize);
/* Mark chosen free block as allocated (split if remainder is useful). */
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
 * insert_free_block - insert block at free-list head.
 *
 * LIFO insertion is O(1) and simple:
 * new -> old_head, old_head->prev = new, head = new.
 */
static void insert_free_block(void *bp)
{
    /* New block's next points to old head. */
    NEXT_FREEP(bp) = free_listp;
    /* New block is head, so prev is NULL. */
    PREV_FREEP(bp) = NULL;

    /* If list was non-empty, old head's prev must point back to new block. */
    if (free_listp != NULL) {
        PREV_FREEP(free_listp) = bp;
    }
    /* Publish new head. */
    free_listp = bp;
}

/*
 * remove_free_block - unlink a block from explicit free list in O(1).
 */
static void remove_free_block(void *bp)
{
    /* If bp has a previous node, bridge prev -> bp->next. */
    if (PREV_FREEP(bp) != NULL) {
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    } else {
        /* Otherwise bp is list head, so move head forward. */
        free_listp = NEXT_FREEP(bp);
    }

    /* If bp has next node, bridge next->prev to bp->prev. */
    if (NEXT_FREEP(bp) != NULL) {
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    }
}

/* extend_heap - request more heap space from memlib and create one free block.
 */
static void *extend_heap(size_t words)
{
    /* bp will be payload pointer of newly created free block. */
    char *bp;
    /* Keep heap aligned by allocating even number of words. */
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    /* Ensure new free block can hold free-list pointers if needed later. */
    if (size < MINBLOCKSIZE) {
        size = MINBLOCKSIZE;
    }

    /* Ask underlying simulated system to grow heap. */
    if ((bp = mem_sbrk((int)size)) == (void *)-1) {
        return NULL;
    }

    /* New free block header. */
    PUT(HDRP(bp), PACK(size, 0));
    /* New free block footer. */
    PUT(FTRP(bp), PACK(size, 0));
    /* New epilogue header immediately after the new free block. */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* Coalesce with previous tail block if it was free. */
    return coalesce(bp);
}


/*
 * coalesce - merge current free block with adjacent free blocks.
 *
 * Case 1: prev alloc, next alloc -> no merge.
 * Case 2: prev alloc, next free  -> merge with next.
 * Case 3: prev free,  next alloc -> merge with prev.
 * Case 4: prev free,  next free  -> merge all three.
 *
 * In all cases, the final merged free block is inserted into free list.
 */

// static void *coalesce(void *bp)
// {
//     /* Allocation status of neighbor blocks. */
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//     /* Current block size before merge. */
//     size_t size = GET_SIZE(HDRP(bp));

//     /* Case 1: nothing to merge. */
//     if (prev_alloc && next_alloc) {
//         return bp;
//     /* Case 2: merge with next block. */
//     } else if (prev_alloc && !next_alloc) {
//         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(HDRP(bp), PACK(size, 0));
//         PUT(FTRP(bp), PACK(size, 0));
//     /* Case 3: merge with previous block. */
//     } else if (!prev_alloc && next_alloc) {
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//         PUT(FTRP(bp), PACK(size, 0));
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//         bp = PREV_BLKP(bp);
//     /* Case 4: merge previous + current + next. */
//     } else {
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
//         bp = PREV_BLKP(bp);
//     }
//     return bp;
// }



static void *coalesce(void *bp)
{
    /* Check allocation bit of physically previous block. */
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    /* Check allocation bit of physically next block. */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /* Current block size before any merge. */
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: both neighbors allocated -> just insert current free block. */
    if (prev_alloc && next_alloc) {
        insert_free_block(bp);
        return bp;
    }

    /* Case 2: merge with next free block. */
    if (prev_alloc && !next_alloc) {
        /* Next block is in free list; remove before structural modification. */
        remove_free_block(NEXT_BLKP(bp));
        /* Combined size = current + next block size. */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        /* Write merged header/footer at current block boundaries. */
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        /* Insert merged block into free list. */
        insert_free_block(bp);
        return bp;
    }

    /* Case 3: merge with previous free block. */
    if (!prev_alloc && next_alloc) {
        /* Previous block is in free list; remove before merge. */
        remove_free_block(PREV_BLKP(bp));
        /* Combined size = previous + current. */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        /* Footer of merged block is current footer position. */
        PUT(FTRP(bp), PACK(size, 0));
        /* Header of merged block is previous header position. */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        /* New block pointer becomes previous block. */
        bp = PREV_BLKP(bp);
        /* Insert merged result into free list. */
        insert_free_block(bp);
        return bp;
    }

    /* Case 4: merge previous + current + next. */
    /* Remove both adjacent free blocks from free list first. */
    remove_free_block(PREV_BLKP(bp));
    remove_free_block(NEXT_BLKP(bp));
    /* Compute total merged size. */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
    /* Merged header written at previous header. */
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    /* Merged footer written at next footer. */
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    /* Canonical pointer to merged block is previous block. */
    bp = PREV_BLKP(bp);
    /* Insert merged block into free list. */
    insert_free_block(bp);
    return bp;
}
/*
 * find_fit - first-fit search in explicit free list.
 */
static void *find_fit(size_t asize)
{
    /* Iterate free blocks from list head to tail. */
    char *bp;

    for (bp = free_listp; bp != NULL; bp = NEXT_FREEP(bp)) {
        /* Found first block large enough for adjusted size. */
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
    }
    /* No block can satisfy request. */
    return NULL;
}

/*
 * place - consume a free block for allocation.
 *
 * If remainder after allocation is large enough, split and keep tail free.
 */
static void place(void *bp, size_t asize)
{
    /* Current free block size before placement. */
    size_t csize = GET_SIZE(HDRP(bp));
    /* Bytes left after carving requested block. */
    size_t remain = csize - asize;

    /* Remove this block from free list since it will be allocated now. */
    remove_free_block(bp);

    /* Split only if remainder can form a valid free block. */
    if (remain >= MINBLOCKSIZE) {
        /* Write allocated block metadata in front part. */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* Move to payload of tail remainder block. */
        bp = NEXT_BLKP(bp);
        /* Mark tail remainder as free block. */
        PUT(HDRP(bp), PACK(remain, 0));
        PUT(FTRP(bp), PACK(remain, 0));
        /* Coalesce tail with its next neighbor if possible, then insert free list. */
        coalesce(bp);
    } else {
        /* Remainder too small: allocate whole block to avoid tiny fragments. */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload.
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
 * mm_free - Free a block and coalesce if possible.
 */
void mm_free(void *ptr)
{
    /* Original block size to preserve while flipping alloc bit. */
    size_t size;

    /* Ignore free(NULL), consistent with libc semantics. */
    if (ptr == NULL) {
        return;
    }

    /* Read block size from current header. */
    size = GET_SIZE(HDRP(ptr));
    /* Mark header as free. */
    PUT(HDRP(ptr), PACK(size, 0));
    /* Mark footer as free. */
    PUT(FTRP(ptr), PACK(size, 0));
    /* Merge with adjacent free blocks and insert merged result into free list. */
    coalesce(ptr);
}

/*
 * mm_realloc - Resize block while preserving old contents.
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    size_t copySize;
    char *newptr;

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

