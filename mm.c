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
#include <stdbool.h>
#include "mm.h"
#include "memlib.h"
#include "contracts.h"
/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) //{printf(__VA_ARGS__); printf("*****in %s*****\n",__func__);}
# define dbg_heapCheck(...) mm_checkheap(__VA_ARGS__)
# define dbg_assert(...) assert(__VA_ARGS__)
#else
# define dbg_printf(...)
# define dbg_heapCheck(...)
# define dbg_assert(...)
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
#define HALF 4
#define WSIZE 8
#define DSIZE 16
#define MIN_BLK_SIZE 24 //header+footer+prev+next
#define TB_LEN 20 //table length = 20
#define SPL_TOR 1


#define CLASS1_MIN (1<<12)
#define CLASS1_MAX (1<<31)
#define CLASS2_MIN (1<< 6)
#define CLASS2_MAX (CLASS3_MIN-1)
#define CLASS3_MIN MIN_BLK_SIZE
#define CLASS3_MAX (CLASS2_MIN-1)


#define CHUNKSIZE (1<<9) //extend the heap by CHUNKSIZE
#define MAX(x,y) ((x)>(y)? (x) : (y))
#define ADJUST(s) ((s)>16? (8+8*(3+(((s)-17)/8))) : (24))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(long int *)(p))
#define PUT(p, val)     (*(long int *)(p) = (val))
#define HALFGET(p)      (*(int *)(p))
#define HALFPUT(p,val)  (*(int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (HALFGET(p) & ~0x7)
#define GET_ALLOC(p) (HALFGET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - HALF)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - HALF)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - WSIZE)))

/* Given block ptr bp, compute the address of the prev and next in list */
#define NEXTP(bp) ((char**)((bp) + WSIZE))
#define PREVP(bp) (char**)((bp))

/* end my macros */

/* global variables */

char* heap_listp;
void** table;
int addIndex;

/* function declarations*/

int mm_init(void);
void* extend_heap(size_t words);

void* malloc(size_t size);
void free(void* ptr);
void* realloc(void* ptr,size_t size);
void* calloc(size_t nmemb,size_t size);
void mm_checkheap(int verbose);

 int getIndex(size_t size);
 void tableAdd (char* bp);
 void place (char* bp, size_t size);
 char* find_fit (size_t size);
 char* split(void* block, size_t size,int index);
 void* coalesce (char* bp);
/*
 * zeros all mem from start to end
 */

 inline void zeros(void* start, void* end){
    int* head = (int*) start;
    int* tail = (int*) end;
    while(head < tail){
        *head = 0;
        head = head +1;
    }
    *tail = 0;
    return;
}


/*
 * helper for pointer arith
 * take out the block from the seglist table
 *
 */
inline void takeOut(char* ptr){ 
    //change the previous and next block in the table
    dbg_assert(ptr !=NULL);
    char** prev_list = PREVP(ptr);
    char** next_list = NEXTP(ptr);

    dbg_printf("ptr %p pl %p, nl %p\n",ptr,*prev_list,*next_list);
    if(*prev_list != NULL && *next_list == NULL){
         dbg_printf("my method: %p\n",NEXTP(*prev_list));
         char** temp = NEXTP(*prev_list); 
         *temp = NULL;
         *prev_list = NULL;
         dbg_printf("pn %p\n",NEXTP(*prev_list));
         return;
        } 
    else if (*prev_list == NULL && *next_list == NULL){ 
         //list had only one elem
         table[getIndex(GET_SIZE(HDRP(ptr)))] = NULL;
         *prev_list = NULL;
         *next_list = NULL;
         return;
        }
    else if(*prev_list == NULL && *next_list != NULL){
         
         //the first one in the list
         char* bp = (char*) ptr;
         dbg_printf("case 3 next_list%p,bp%p\n",*next_list,bp);
         table[getIndex(GET_SIZE(HDRP(bp)))] = *next_list;
         
         char** temp = PREVP(*next_list); 
         *temp = NULL;
         *next_list = NULL;
         return;
        }
    else{
      //if(prev_list != NULL && next_list != NULL){
            char** temp1 = NEXTP(*prev_list);
            char** temp2 = PREVP(*next_list);
            *temp1 = *next_list;
            *temp2 = *prev_list;
            *next_list = NULL;
            *prev_list = NULL;
            return;
        }
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(22*WSIZE+HALF)) == (void *)-1){
      dbg_printf("init problem\n");
      return -1;
    }
   
    /* the first 20 blocks are table entries NULL-ed*/
    table = (void**)heap_listp;
    int i;
    for (i=0;i<20;i++){
        table[i] = NULL;
    }

    heap_listp += (20*WSIZE);

    HALFPUT(heap_listp,0);  /* offset blk */

    HALFPUT(heap_listp + HALF , PACK(WSIZE, 1)); /* Prologue header */
    HALFPUT(heap_listp + WSIZE, PACK(WSIZE, 1)); /* Prologue footer */
    HALFPUT(heap_listp + WSIZE + HALF, PACK(0, 1));      /* Epilogue header */
    //heap_listp points to prilogue after init

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    dbg_printf("exiting from init\n"); 
    return 0;
}

/* 
 * helper function for init
 * extends heap by words
 */
inline void *extend_heap(size_t words) {
    char *bp;
    size_t size = words*WSIZE;

    //if((long unsigned)mem_heap_hi()+(long unsigned) size > (long unsigned)heap_max) return NULL; 
    /* use mem_sbrk to allocate new heap */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    //dbg_printf("new bp:%p,heap_max:%p,heap_listp:%p\n",bp,heap_max,heap_listp);
   
    bp = bp - HALF;
    /* Initialize free block header/footer and the epilogue header */
    HALFPUT(HDRP(bp), PACK(size,0));        /* Free block header(previous epilogue)*/
    dbg_printf("hd:%d\n",HALFGET(HDRP(bp)));
    HALFPUT(FTRP(bp), PACK(size,0));        /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));     /* New epilogue*/
    dbg_printf("bp:%p,hd:%p,ft:%p,ep:%p\n",bp,HDRP(bp),FTRP(bp),HDRP(NEXT_BLKP(bp)));
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * helper function for coalesce
 */

inline void* coalesce (char* bp) {
    dbg_assert(GET_ALLOC(HDRP(bp))==0);
    
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    dbg_printf("prev_alloc:%d,next_alloc:%d\n",(int)prev_alloc,(int)next_alloc);
    //case 1
    if (prev_alloc && next_alloc) {
        dbg_printf("nothing happends\n");
        tableAdd(bp);
        dbg_heapCheck(1);
        return bp;
    }
    //case 2
    if (prev_alloc && !next_alloc) {
        //takes out the next blk after bp
        takeOut(NEXT_BLKP(bp)); 
        size_t size = GET_SIZE(HDRP(bp));

        //takes care of the physical adr stuff
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        HALFPUT(HDRP(bp), PACK(size, 0));
        HALFPUT(FTRP(bp), PACK(size,0));
    }

    //case 3
    else if (!prev_alloc && next_alloc) {
        takeOut(PREV_BLKP(bp));
        size_t size = GET_SIZE(HDRP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        HALFPUT(FTRP(bp), PACK(size, 0));
        HALFPUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    //case 4
    else { 
        takeOut(PREV_BLKP(bp));
        takeOut(NEXT_BLKP(bp));
        size_t size = GET_SIZE(HDRP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        HALFPUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        HALFPUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //re-add coalesced bp
    tableAdd(bp);
    dbg_printf("before check\n");
    dbg_heapCheck(1);
    dbg_printf("passed check in coal\n");
    return bp;

}
/* 
 * Uses the 20 blocks as a lookup table, covering different size of requests
 * Class 3: index 0 - 3; size 32B - 56B
 * Class 2: index 4 - 9; size 1<<6 - 1<<12 -1
 * Class 1: index 10-19; size 1<<12 - 1<<32
 * 
 * attempt 2:
 * class 3: index 0 - 4: 24 - 56
 * class 2: index 5 -10: 1<<6 - 1<<12-1
 * class 1: index 11-19: 1<<12 - 1<<32-1
 *
 */
inline int getIndex(size_t size){
    int index = -1;    
    int i;
    int map;
    
    dbg_printf("size to look up: %d\n",(int)size);
    if (size >= CLASS1_MIN){
        //in class 1 get highest bit
        dbg_printf("in class 1\n");
        
        for(i=31;i>11;i--){
            map = 1<<i;
            if ((size&map)!=0){
              if (i==30 || i==31){
                index = 19;
              }
              else{
                index = ((i -12)/2)+11;
              }
              break;
            }
        }
    }
    else if (size >= CLASS2_MIN){
        //in class 2 get highest bit        
        dbg_printf("in class 2\n");
        for(i=11;i>5;i--){
            map = 1<<i;
            if((size&map)!=0){
              index = i-1;//i-6+4
              break;
            }
        }
    }
    else{
        //in class 3
        dbg_printf("in class 3\n");
        index = (size -24)/8; 
    }
    dbg_assert(index >= 0 && index < 20);

    return index;
}
/* 
 * adds a free block to the seg list table
 * used when: extending heap, coalescing
 */

inline void tableAdd (char* bp){
    
    int size = GET_SIZE(HDRP(bp));

    dbg_assert(size>=MIN_BLK_SIZE);
    dbg_assert(GET_ALLOC(HDRP(bp))==0);
    int index;

    index = getIndex(size);
    dbg_printf("index to add to %d,bp:%p\n",index,bp);
    if (index ==-1) 
      return;
    addIndex = index;

    char* next = (char*)table[index];
    table[index] = (void*)bp;
    char** prev_list = PREVP(bp);
    dbg_printf("prev list:%p\n",*prev_list);
    *prev_list = NULL;

    char** next_list = NEXTP(bp); 
    dbg_printf("next list:%p\n",*next_list);
    *next_list = next;
    
    dbg_printf("after assignment nl = %p\n",*next_list);
    if (next !=NULL){
      dbg_printf("should be here\n");
      char** prev_next = PREVP(*next_list);
      *prev_next = bp;
    }
    dbg_printf("hi from add to table %p,next%p\n",table[index],*next_list);
    return;
}


/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    dbg_printf("requesting size: %d\n",(int)size);
    /* Ignore spurious requests */
    if (size == 0 || size >= (long unsigned)CLASS1_MAX)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. 
     * changed to WSIZE = 8 Bytes
     * asize describes the payload + hearder + footer
     */
    asize = ADJUST(size);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    dbg_printf("going to extend for size:%d\n",(int)asize);
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    //printf("finished malloc size: %d\n",(int)size);
    return bp;
}


/*
 * helper function for malloc: place 
 */

inline void place (char* bp, size_t size) {
    //size is aligned to 8B in malloc
    //unsigned blkSize = GET_SIZE(HDRP(bp));
  
    //dbg_assert(blkSize>=size);
    int index = addIndex;
    
    //take out the blk
    takeOut(bp);
    
    bp = split(bp,size,index);
  
    size = GET_SIZE(HDRP(bp));
    HALFPUT(HDRP(bp),PACK(size,1));
    HALFPUT(FTRP(bp),PACK(size,1));
    dbg_printf("bpuft:%p,prevft:%p\n",FTRP(bp),FTRP(PREV_BLKP(bp)));
    dbg_printf("just placed: hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(bp)),(int)GET_SIZE(HDRP(bp)));
    dbg_printf("prev blk, hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(PREV_BLKP(bp))),(int)GET_SIZE(FTRP(PREV_BLKP(bp)))); 
    dbg_heapCheck(1);
    return;
} 

/*
 * helper function for malloc : find_fit
 */

inline char* find_fit (size_t size){
    int index;
    char** next_list=NULL;
    index = getIndex(size);
    if (index==-1) return NULL;
    
    dbg_assert(index>=0 && index<20);
    
    //take out the first one
    int i=index;
    for(i = index;i<19;i++){
        char* temp = table[i];
        while(temp != NULL){
            if ((size_t)GET_SIZE(HDRP(temp))>=size){
                addIndex=i;
                return temp;
            }
            next_list = NEXTP(temp);
            temp = *next_list;
        }
    }
    //only returns a ptr to the right blk
    //doesn't change ptr around nor split
    dbg_printf("exit from findfit\n");
    return NULL;
    
}
/*
 * takes in a ptr to a payload 
 * split the block if too big 
 * add the split block back to table
 */
inline char* split(void* block, size_t size,int index){ 
    dbg_assert(size>=MIN_BLK_SIZE);
    //don't bother spliting if in class 1
    if (index<6) return (char*)block;
    dbg_assert((size_t)GET_SIZE(HDRP(block))>=size); 
    int diff = GET_SIZE(HDRP((char*)block)) - size;
    
    dbg_printf("diff is %d, blk_size is%d,size is%d\n",diff,(int)GET_SIZE(HDRP(block)),(int)size);


    //SPL_TOR = split tolerance default = 4
    //the higher it is, more utilization less efficiency
    if ((unsigned)diff < (MIN_BLK_SIZE*SPL_TOR)) {
      return (char*)block;
    }
    else {
        //splits into two aligned blocks
        dbg_assert(diff>=MIN_BLK_SIZE);
        HALFPUT(HDRP(block),PACK(size,0));
        HALFPUT(FTRP(block),PACK(size,0));
        dbg_printf("new blk: hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(block)),(int)GET_SIZE(FTRP(block)));
        HALFPUT(HDRP(NEXT_BLKP(block)),PACK(diff,0));
        HALFPUT(FTRP(NEXT_BLKP(block)),PACK(diff,0));
        
        tableAdd(NEXT_BLKP(block));
        dbg_printf("new blk added size:%d\n",(int)GET_SIZE(HDRP(NEXT_BLKP(block))));
        
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
    char** prev_list = PREVP(bp);
    char** next_list = NEXTP(bp);

    HALFPUT(HDRP(bp), PACK(size, 0));
    HALFPUT(FTRP(bp), PACK(size, 0));
    *prev_list = NULL;
    *next_list = NULL;
    dbg_printf("prev_list%p\n",prev_list);
    dbg_printf("next_list%p\n",next_list);
   
    dbg_printf("prev blk size:%d,current size: %d\n",(int)GET_SIZE(HDRP(PREV_BLKP(bp))),(int)size);

    coalesce(bp);
    dbg_heapCheck(1);
    return;
}

inline char* cpy (void* src, void* dest, size_t size){
    char* old = (char*) src;
    char* new = (char*) dest;
    dbg_assert(size%8 == 0);
    size_t i;
    for (i = 0;i<size;i++){
        char olddata = (*old);
        *new = olddata;
        new+=1;
        old+=1;
    }
    return (char*)new+size;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    if (oldptr == NULL) return malloc(size);
    if (size == 0){
        free(oldptr);
        return NULL;
    }
    
    //oldptr is a ptr to a non-freed block
    char* oldbp = (char*) oldptr;
    size_t oldSize = GET_SIZE(HDRP(oldbp));
    int alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldbp)));
    dbg_printf("reallocated size:%d,old size %d\n",(int)size,(int)oldSize);
    

    size = ADJUST(size);
    //for checking second case
    size_t nextSize = GET_SIZE(HDRP(NEXT_BLKP(oldbp)));
    size_t sum = oldSize + nextSize; /* will not overflow */
    char* nextBlk = NEXT_BLKP(oldbp);
    size_t diff = sum - size;
    size_t addition = nextSize - diff;

    //case 1: size <= oldSize
    if (size <= oldSize) {
      dbg_printf("in case one of realloc\n");
      return oldptr;
    }
    //case 2: size > oldSize but free block enough
    else if (alloc == 0 && sum >= size && addition >=MIN_BLK_SIZE){
        //take the old blk and part of the next blk

        takeOut(nextBlk);
        nextBlk = split(nextBlk,addition,getIndex(nextSize));
        size = oldSize + GET_SIZE(HDRP(nextBlk));
        
        dbg_printf("now size is%d\n",(int)size);
        //zeros the diff part
        dbg_printf("passed into zeros: %p,%p \n",FTRP(oldbp),FTRP(nextBlk));
        zeros(FTRP(oldbp),FTRP(nextBlk));
        
        //mark as allocated
        HALFPUT(HDRP(oldbp),PACK(size,1));
        HALFPUT(FTRP(oldbp),PACK(size,1));
        dbg_printf("exit from realloc case 2,bp:%p,size:%d\n",oldbp,(int)GET_SIZE(HDRP(oldbp)));
        return (void*)oldbp;
    }
    //case 3: need to find new blk and copy mem
    else{
        dbg_assert(size>oldSize);
        char* newbp = mm_malloc(size);
        /* not including ft and hd TODO garbled byte use perl.rep */
        char* trash = cpy(oldbp,newbp,(oldSize - WSIZE));
        
        /* not zero-ing the ft of new blk */
        zeros(trash, FTRP(newbp)-HALF);
        free(oldbp);
        dbg_printf("exit from realloc case 3\n");
        return (void*)newbp; 
    }
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    char* bp = malloc(nmemb*size);
    zeros(bp,FTRP(bp)-WSIZE);
    return bp;
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

/* helper for the heap checker
 * returns num of free lists 
 * returns -1 on error
 */
static int valid_list(void* bucket,int index){
    //count number of free blks
    int count = 0;
    char* bp = (char*)bucket;
    if (bp==NULL) return 0; //if nothing is in the list
    
    char** next = NEXTP(bp);

    //check if the size is in the right bucket
    while (bp != NULL) {
        count++;
        dbg_printf("index: %d bp:%p next %p\n",index,bp,*next);
        next = NEXTP(bp);
        int size = GET_SIZE(HDRP(bp)); 
        if(!(getIndex(size)==index)){
            dbg_printf("wrong bucket,size:%d;index:%d,should be:%d,bp:%p\n",size,index,getIndex(size),bp);
            return -1;
        }
        bp = *next;

    }
    return count;
}
/* helper for heap checker 
 * returns num of free lists in total
 * returns -1 on error
 */

static int valid_table(void){
    int countTB = 0;
    int countList = 0;
    
    if (table == NULL){ 
        dbg_printf("table init prob\n"); 
        return -1;
    }
    int i;
    for(i = 0;i<20;i++){
        if((countList = valid_list(table[i],i))==-1){
            dbg_printf("list prob:%d\n",i);
            return -1;
        }
        else {
            countTB += countList;
        }
    }
    return countTB;
}


/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    //always verbose
    verbose = verbose;
    
    //counting free lists
    int intern_count;
    int out_count;
    intern_count = 0;
    out_count=0;
    char* current = heap_listp;
    char* next = current + 2*WSIZE;
    int preAlloc = -1; //invalid at beginning checks if coalescing is good

    if (current==NULL){ 
        dbg_printf("starting pointers NULL\n");
        exit(1);
    }

    if(HALFGET(current)!=0){
        dbg_printf("free offset problem\n");
        exit(1);
    }

    if (current != ((char*)table+20*WSIZE)){
        dbg_printf("table length problem\n");
        exit(1);
    }
    
    //check prologue
    current += HALF;
    if(GET_SIZE(current)!=8 || GET_ALLOC(current)!=1
        || GET_SIZE(current+HALF)!=8 || GET_ALLOC(current+HALF)!=1){
        dbg_printf("prologue wrong\n");
        exit(1);
    }

    //check everything else in the middle
    while(!(GET_SIZE(HDRP(next)) == 0 && GET_ALLOC(HDRP(next))==1)){ //epilogue
        
        current = next;
        next = NEXT_BLKP(current);
        if (GET_ALLOC(HDRP(current))==0) intern_count++;
        

        //1.checks footer header consistency
        int sizeH = GET_SIZE(HDRP(current));
        int sizeF = GET_SIZE(FTRP(current));
        int allocH = GET_ALLOC(HDRP(current));
        int allocF = GET_ALLOC(FTRP(current));
        dbg_printf("%d,%d,%d,%d\n",sizeH,sizeF,allocH,allocF);
        if (sizeH != sizeF || allocH != allocF){
            dbg_printf("H-F problem\n");
            exit(1);
        }

        //2.checks alignment
        if (!aligned((void*)current)){
            dbg_printf("alignment problem\n");
            exit(1);
        }

        //3.checks heap boundaries
        if (!in_heap((void*)current)){
            dbg_printf("outside heap %p,high:%p,low:%p\n",current,mem_heap_hi(),mem_heap_lo());
            exit(1);
        }
            
        //4.checks coalescing
        if (preAlloc == allocH){
            dbg_printf("coalescing problem\n");
            exit(1);
        }
    }
    
    dbg_printf("checking seg list,out_count %d\n",out_count);   
    //check the seg list
    if ((out_count = valid_table())==-1){
        dbg_printf("table problem %d\n",out_count);
        exit(1);
    }else if (out_count != intern_count) {
            dbg_printf("num of free lists not same,in %d;out %d\n",intern_count,out_count);
            exit(1);  
      }

    return;
}
