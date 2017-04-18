#include <stdio.h>
#include <stdlib.h>
#include "gc.h"

extern value body(void);

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

void maincont_code(void) {
  value y = args[1];
  printtree(stdout, y);
  exit(0);
}

value maincont[2] = {(value)maincont_code, 0};

int main(int argc, char *argv[]) {
  body();
  maincont_code();
  return 0;
}
