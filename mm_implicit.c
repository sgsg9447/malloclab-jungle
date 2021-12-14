/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "1 team",
    /* First member's full name */
    "Kim seulgi",
    /* First member's email address */
    "sgsg9447@gmail.com",
    /* Second member's full name (leave blank if none) */
    "lee jong ho, park hyun woo", 
    /* Second member's email address (leave blank if none) */
    "hh"
};

// /* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x)>(y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p)) 
#define PUT(p,val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE) //char는 1바이트니까 형변환을해줘야해
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))


static void* heap_listp;
static void* last_listp; //next-fit의 검색 종료지점을 찾기위해 전역변수 선언

/* 
 * mm_init - initialize the malloc package.
 */
static void* coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //case1 위아래 alloc
    if(prev_alloc && next_alloc)
    {
        return bp;
    }

    //case2 prev는 alloc 이고 next는 free일때
    else if(prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }

    //case3 prev는 free이고 next는 alloc일때
    else if(!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    //case4 위아래 free
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    last_listp = bp;

    return bp;

}

static void* extend_heap(size_t words)
{
    char * bp;
    size_t size;
    // 짝수는 나머지 0이니까 0일때 False
    size = (words % 2) ? (words+1)*WSIZE : words * WSIZE;
    if((long)(bp= mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0)); //Free block header
    PUT(FTRP(bp), PACK(size, 0)); //Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); //New epilogue header

    return coalesce(bp);

}


int mm_init(void)
{
    // 아무 의미없는 패딩 >> 1word
    // prolog block >> header , footer 로만 구성 각 1word 씩 2word
    // eplilog block >> header로만 구성 1word
    //heap_listp를 4워드 만큼 늘릴거야 이걸 실패하면 -1이겠지 그렇다면 리턴-1
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1)
    {
        return -1;
    }
    //성공했어! unused
    PUT(heap_listp,0);
    //Prologue header
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    //Prologue footer
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    //Epilogue header
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    //늘 prologue header 가리키겟지!
    heap_listp += (2*WSIZE);
    last_listp = heap_listp;

    //이제 늘려야겠지
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

// static void * find_fit(size_t asize) 
// {
//     //first-fit search
//     void *bp;

//     //epilogue header만나면 사이즈 0이니까 끝나겠지
//     for(bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp))
//     { //프리한상태이고 asize가 들어갈수있을때
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//         {
//             return bp;
//         }
//     }
//     return NULL; //No fit
// }


static void * find_fit(size_t asize) 
{
    //next-fit search
    void *bp;
    //epilogue header를 만나기 전까지 돌아간다.
    for(bp = last_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp))
    { //프리한상태이고 asize가 들어갈수있을때
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_listp = bp;
            return bp;
        }

    }
    //처음부터 보기
    for(bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_listp = bp;
            return bp;
        }
    }
    return NULL; //No fit
}


static void place(void* bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    //최소 16이니까 16보다 크냐!
    if ((csize - asize) >= (2*DSIZE)) //분할을 할 수있는 조건이 되면
    {
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else 
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{   
    //배치
    //first fit , next fit, best fit
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize; //adjusted block size //3을넣어도 8이되고 11을넣어도 16이 될거니까 조정된 블럭사이즈다 ! 블록은 8의배수만큼늘어나니까
    size_t extendsize;
    char *bp;

    if (size == 0)
    {
        return NULL;
    }

    if (size <= DSIZE)
    {
        //최소 16이니까
        asize = 2*DSIZE;
    }
    else
    {
        //8의배수가 나오는 거겠네~~
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    //No fit
    //힙을 늘려야겠지
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    //블럭에서 헤더랑 푸터 존재.... >>coalesce (합치다) 뭘합쳐 ? 가용블록들을!
    //인접블록이 가용블록이면 coalesce를 한다.
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
//이미 할당된 블럭 사이즈를 직접 건드리는 것이 아니라, 임시로 요청 사이즈만큼의 블록을 만들고 현재의 블록을 반환하는 것이다. 그러면 사이즈를 변경한 효과가 나기 때문이다.
//1. 요청 사이즈가 0보다 작거나 같으면 반환을 해도 되니 반환을 해버린다.
//2. 위치가 없다면 malloc 을 통해 새롭게 사이즈만큼 생성한다. (예외처리의 일종)
//3. 요청 사이즈가 기존 사이즈보다 작으면 요청 사이즈만큼의 데이터만 잘라서 옮긴다.

void *mm_realloc(void *bp, size_t size)
{   
    if(size <=0)
    {   
        mm_free(bp);
        return 0;
    }

    if(bp == NULL)
    {
        return mm_malloc(size);
    }

    void * newp = mm_malloc(size);
    if(newp == NULL)
    {
        return 0;
    }

    size_t copySize = GET_SIZE(HDRP(bp));
    if (size < copySize)
    {
        copySize = size;
    }
    memcpy(newp, bp, copySize); 
    mm_free(bp);
    return newp;
}














