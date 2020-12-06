#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>

extern value body(struct thread_info *);

extern value args[];

extern value maincont[];

static void printtree_body(FILE *f, value v) {
  if(Is_block(v)) {
    if ((unsigned int)v > (unsigned int)(maincont)) {
      header_t hd = Field(v,-1);
      int sz = Wosize_hd(hd);
      int i;
      fprintf(f,"%d(", Tag_hd(hd));
      for(i=0; i<sz-1; i++) {
	printtree_body(f,Field(v,i));
	fprintf(f,",");
      }
      if (i<sz)
	printtree_body(f,Field(v,i));
      fprintf(f,")");
    }
    else {
      fprintf(f,"%8x",v);
    }
  }
  else fprintf(f,"%d",v>>1);
}

static void printtree(FILE *f, value v) {
  printtree_body(f, v);
  fprintf(f, "\n");
}


/* halt x is extracted to set args[1] to x */
void maincont_code(struct thread_info *tinfo) {
  unsigned int *args;
  args = tinfo->args;
  value y = args[1];
  printtree(stdout, y);
  exit(0);
}



/*
OS: Checks if an int represents a pointer, implemented as an extern in Clight
 */
_Bool is_ptr(unsigned int s) {
  return (_Bool) Is_block(s);
} 



value maincont[2] = {(value)maincont_code, 0};

int main(int argc, char *argv[]) {
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;

  tinfo = make_tinfo();
  start = clock();
  body(tinfo);
  end = clock();

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  maincont_code(tinfo);
  return 0;
}
