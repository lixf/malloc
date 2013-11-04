/* Xiaofan Li
 * xli2
 * 18213 f13
 * mallocLab 
 *
 *
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* my macros*/

#define WSIZE 8
#define DSIZE 16
#define MIN_BLK_SIZE 32 //header+footer+prev+next
#define TB_LEN 20 //table length = 20
#define CLASS3_MIN (1<<12)
#define CLASS3_MAX (1<<32)
#define CLASS2_MIN (1<< 7)
#define CLASS2_MAX (CLASS3_MIN-1)
#define CLASS1_MIN MIN_BLK_SIZE
#define CLASS1_MAX (CLASS2_MIN-1)


#define CHUNKSIZE (1<<12) //extend the heap by CHUNKSIZE
#define MAX(x,y) ((x)>(y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* end my macros */

/* global variables */

static char* heap_listp;
static void** table;



/* function declarations*/

int mm_int(void);
static void* extend_heap(size_t words);

void* malloc(size_t size);
void free(void* ptr);
void* realloc(void* ptr,size_t size);
void* calloc(size_t nmemb,size_t size);
void mm_checkheap(int verbose);

static void place (char* bp, size_t size);
static void* find_fit(size_t size);
static int aligned(const void *p);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
 
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(24*WSIZE)) == (void *)-1)
      printf("init problem");
      return -1;
    
    /* the first 20 blocks are table entries NULL-ed*/
    table = heap_listp;
    int i;
    for (i=0;i<20;i++){
        table[i] = NULL;
    }

    PUT(heap_listp + (20*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (21*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (22*WSIZE), PACK(0, 1));      /* Epilogue header */
    //heap_listp points to prilogue after init
    heap_listp += (20*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    

    //add the free block into the table
    tableAdd(heap_listp+(2*WSIZE));
    return 0;
}

/* 
 * helper function for init
 * extends heap by words
 */
static void *extend_heap(size_t words) {
    char *bp;

    /* use mem_sbrk to allocate new heap */
    if ((long)(bp = mem_sbrk(words)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(words,0));      /* Free block header(previous epilogue)*/
    PUT(FTRP(bp), PACK(words,0));      /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));/* New epilogue*/

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * helper function for coalesce
 */

static void coalesce (char* bp) {

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //case 1
    if (prev_alloc && next_alloc) {
        return bp;
    }
    
    //case 2
    else if (prev_alloc && !next_alloc) {
        //take out the next block from table
        void* next = NEXT_BLKP(bp);
        //change pointers
        (*((*next)+1)) = *(next+1);
        //set the previous free block point to the next one
        
        //also set the prev of the next to point to the previous
        (*(*(next+1))) = *next;

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    //case 3
    else if (!prev_alloc && next_alloc) {
        void* last = PREV_BLKP(bp);
        //same as above
        (*((*last)+1)) = *(last+1);
        (*(*(last+1))) = *last;
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    //case 4
    else {
        
        void* next = NEXT_BLKP(bp);
        void* last = PREV_BLKP(bp);
        (*((*next)+1)) = *(next+1);
        (*(*(next+1))) = *next;
        (*((*last)+1)) = *(last+1);
        (*(*(last+1))) = *last;

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //re-add coalesced bp
    tableAdd(bp);
    mm_checkheap(1);

    return bp;

}

int getIndex(size_t size){
    
    int index = -1;
    //check for class
    if (size > CLASS3_MAX){
        printf("block too big!\n");
        exit(1);
    } 
    else if (size > CLASS3_MIN){
        //in class 3 get highest bit
        int i;
        for(i=32;i>11;i--){
            int map = 1<<i;
            if ((size&map)==1){
              index = ((i -12)/2)+10;
              break;
            }
        }
    }
    else if (size > CLASS2_MIN){
        //in class 2 get highest bit
        int i;
        for(i=11;i<5;i--){
            int map = 1<<i;
            if((size&map)==1){
              index = i-2;//i-6+4
              break;
            }
        }
    }
    else{
        //in class 3
        index = (size -32)/8; 
    }

    return index;
}
/* 
 * adds a free block to the seg list table
 * used when: extending heap, coalescing
 */

void tableAdd (char* bp){
    int size = GET_SIZE(HDRP(bp));
    ASSERT(size>MIN_BLK_SIZE);
    ASSERT(GET_ALLOC((HDRP(bp))==0));
    int index;

    index = getIndex(size);
    ASSERT (index>=0 && index<20);

    //change the table[index]
    void* next = table[index];
    table[index] = bp;
    *bp = NULL;
    *(bp + WSIZE) = next;
    *next = bp;
    return;
}


/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;


    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. 
     * changed to WSIZE = 8 Bytes
     * asize describes the payload
     */
    if (size <= WSIZE)
        asize = WSIZE;
    else
        asize = WSIZE * ((size + (WSIZE) + (WSIZE-1)) / WSIZE);


    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * helper function for malloc: place 
 * careful! size is the size of payload TODO 
 */

void place (char* bp, size_t size) {
  //size is aligned to 8B in malloc
  int blkSize = GET_SIZE(HDRP(bp));
  int rest = blkSize - size -16;//excluding header and footer
  ASSERT(rest > 0);


  if (rest >= MIN_BLK_SIZE){
      PUT(HDRP(NEXT_BLKP(bp)),PACK(rest,0));
      PUT(FTRP(NEXT_BLKP(bp)),PACK(rest,0));
  }
  
  PUT(HDRP(bp),PACK(size,1));
  PUT(FTRP(bp),PACK(size,1));

} 

/*
 * helper function for malloc : find_fit
 */

char* find_fit (size_t size){
    int index;
    index = getIndex(size);
    if (index==-1) return NULL;
    
    ASSERT(index>=0 && index<20);
    
    //take out the first one
    void* temp = table[index];
    void* next = *(temp+1);
    table[index] = next;
    *next = NULL;
    
    //might need to split
    return split(temp,size,index);

}

char* split(void* block, size_t size,int index){
    if (index<4) return (char*)block;
    
    int diff = GET_SIZE(HDRP((char*)block)) - size;
    if (diff < (size/2)) return (char*)block;
    else {
        //splits into two aligned blocks
        PUT(HDRP(block),PACK(size+2*WSIZE,0));
        PUT(FTRP(block),PACK(size+2*WSIZE,0));
        PUT(HDRP(NEXT_BLKP(block)),PACK(diff-2*WSIZE,0));
        PUT(FTRP(NEXT_BLKP(block)),PACK(diff-2*WSIZE,0));
        
        tableAdd(NEXT_BLKP(block));
        return (char*)block;
    }
}



/*
 * free
 */
void free (void* ptr) {
    if (!ptr) return;

    char* bp = ptr;
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    coalesce(bp);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    return NULL;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}




static int valid_list(void* bucket,int sizeMin,int sizeMax){
    //count number of free lists
    int count = 0;
    char* bp = bucket;
    if (bp==NULL) return 0; //if nothing is in the list
    
    char* next = bp + WSIZE;

    //check if the size is in the right bucket
    while (bp != NULL) {
        count++;
        int size = GET_SIZE(HDRP(bp)); 
        if(!(size >= sizeMin && size <= sizeMax)){
            printf("wrong bucket\n");
            return -1;
        }
        bp = next;
        next = *(bp+WSIZE);
    }
    return count;
}


static int valid_table(void){
    int countTB;
    int countList;
    
    if (table == NULL) 
        printf("table init prob"\n);
        return -1;
    int i;
    for(i = 0;i<tb_len;i++){
        if((countList = valid_list(table[i],min,max))==-1){
            printf("list prob"\n);
            return -1;
        }
        else {
            countTB += countList;
    }
    return countTB;
}


/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    //counting free lists
    int intern_count=0;
    int out_count=0;
    char* current = heap_listp;
    char* next = current + 3*WSIZE;
    int preAlloc = -1; //invalid at beginning

    if (current==NULL || next==NULL) 
        printf("starting pointers NULL\n");
        exit(1);

    //check prologue
    if(GET_SIZE(current)!=16 || GET_SIZE(current+WSIZE)!=16
        || GET_ALLOC(current)!=1 || GET_ALLOC(current+WSIZE)!=1)
        printf("prologue wrong\n");
        exit(1);


    //check everything else in the middle
    while(GET_SIZE(next) != 0){ //epilogue
        
        current = next;
        next = NEXT_BLKP(current);
        intern_count++;


        //1.checks footer header consistency
        int sizeH = GET_SIZE(HDRP(current));
        int sizeF = GET_SIZE(FTRP(current));
        int allocH = GET_ALLOC(HDRP(current));
        int allocF = GET_ALLOC(FTRP(current));
        if (sizeH != sizeF || allocH != allocF)
            printf("H-F problem\n");
            exit(1);

        //2.checks alignment
        if (!aligned((void*)current))
            printf("alignment problem\n");
            exit(1);

        //3.checks heap boundaries
        if (!in_heap((void*)current))
            printf("outside heap\n")
            exit(1);
            
        //4.checks coalescing
        if (preAlloc == allocH)
            printf("coalescing problem"\n);
            exit(1);
        
    }
    
    
    //check the seg list
    if ((out_count = valid_table())==-1){
        printf("table problem"\n);
        exit(1);    
      }
    else {
        if (out_count != intern_count) 
            printf("num of free lists\n");
            exit(1);  
      }

    return;
}
