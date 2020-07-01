#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include "gc.h"
#include <pcre.h>

extern value body(struct thread_info *);
extern value args[];

/* extern struct thread_info; */
extern unsigned int get_Coq_Strings_String_string_tag(value);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(value);
extern unsigned int get_Coq_Init_Datatypes_list_tag(value);
extern unsigned int get_CertiCoq_Benchmarks_regex_regex_rgx_tag(value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern value make_Coq_Init_Datatypes_unit_tt(void);
extern value make_Coq_Init_Datatypes_list_nil(void);
extern value make_Coq_Strings_String_string_EmptyString(void);
extern value make_Coq_Init_Datatypes_option_None(void);
extern value alloc_make_Coq_Strings_Ascii_ascii_Ascii(struct thread_info *, value, value, value, value, value, value, value, value);
extern value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, value arg0, value arg1);
extern value alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, value);
extern value alloc_make_Coq_Strings_String_string_String(struct thread_info *, value, value);

extern value alloc_make_CertiCoq_Benchmarks_regex_regex_RegexFFI_Build_RegexFFI(struct thread_info *, value, value);
extern value make_CertiCoq_Benchmarks_regex_regex_RegexFFI_Build_RegexFFI(value, value, value *);

extern value *call(struct thread_info *, value, value);

extern value const rgx_test_clo[2];
extern value const rgx_exec_clo[2];

#define MIN(x, y) (((x) < (y)) ? (x) : (y))

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

unsigned char ascii_to_char(value x) {
  unsigned char c = 0;
  for(unsigned int i = 0; i < 8; i++) {
    unsigned int tag = 
      get_Coq_Init_Datatypes_bool_tag(*((value *) *((value *) x) + i));
    c += !tag << i;
  }
  return c;
}


typedef enum { EMPTYSTRING, STRING } coq_string;

size_t string_value_length(value s) {
  value temp = s;
  size_t i = 0;
  while(get_Coq_Strings_String_string_tag(temp) == STRING) {
    temp = *((value *) temp + 1ULL);
    i++;
  }
  return i;
}

char *value_to_string(value s) {
  value temp = s;
  char * result;
  size_t result_length = string_value_length(s) + 1;
  result = (char*) malloc(result_length * sizeof(char));
  memset(result, 0, result_length);

  for(int i = 0; get_Coq_Strings_String_string_tag(temp) == STRING; i++) {
    sprintf(result + i, "%c", ascii_to_char(temp));
    temp = *((value *) temp + 1ULL);
  }

  return result;
}

typedef enum {
  EMPTY, EPSILON, LITERAL, OR, AND, STAR, CAPTURE
} rgx;

size_t regex_string_size(value r) {
  char *lit;
  switch(get_CertiCoq_Benchmarks_regex_regex_rgx_tag(r)) {
    case EMPTY:
      return 4;
    case EPSILON:
      return 4;
    case LITERAL:
      lit = value_to_string(*((value *) r));
      return 4 + strlen(lit);
    case OR:
      return 5 + regex_string_size(*((value *) r + 0)) + regex_string_size(*((value *) r + 1));
    case AND:
      return 4 + regex_string_size(*((value *) r + 0)) + regex_string_size(*((value *) r + 1));
    case STAR:
      return 5 + regex_string_size(*((value *) r + 0));
    case CAPTURE:
      return 2 + regex_string_size(*((value *) r + 0));
  }
  return 0;
}

void regex_to_string_aux(value r, char *s) {
  char *lit;
  switch(get_CertiCoq_Benchmarks_regex_regex_rgx_tag(r)) {
    case EMPTY:
      strcat(s, "(?!)");
      return;
    case EPSILON:
      strcat(s, "(?:)");
      return;
    case LITERAL:
      strcat(s, "(?:");
      lit = value_to_string(*((value *) r));
      strcat(s, lit);
      strcat(s, ")");
      return;
    case OR:
      strcat(s, "(?:");
      regex_to_string_aux(*((value *) r + 0), s);
      strcat(s, "|");
      regex_to_string_aux(*((value *) r + 1), s);
      strcat(s, ")");
      return;
    case AND:
      strcat(s, "(?:");
      regex_to_string_aux(*((value *) r + 0), s);
      regex_to_string_aux(*((value *) r + 1), s);
      strcat(s, ")");
      return;
    case STAR:
      strcat(s, "(?:");
      regex_to_string_aux(*((value *) r), s);
      strcat(s, ")*");
      return;
    case CAPTURE:
      strcat(s, "(");
      regex_to_string_aux(*((value *) r), s);
      strcat(s, ")");
      return;
  }
}

void regex_to_string(value r, char *s) {
  /* strcat(s, "^"); */
  regex_to_string_aux(r, s);
  /* strcat(s, "$"); */
}

value rgx_test(struct thread_info *tinfo, value r, value str) {
  int OVECCOUNT = 20;
  pcre *re;
  const char *error;
  int erroffset;
  int ovector[OVECCOUNT];
  int rc;

  size_t rs_size = regex_string_size(r);
  char *rs = (char *) malloc(rs_size * sizeof(char));
  regex_to_string(r, rs);
  char *matched = value_to_string(str);


  re = pcre_compile(
      rs,         /* the pattern */
      0,          /* default options */
      &error,     /* for error message */
      &erroffset, /* for error offset */
      NULL);      /* use default character table */

  rc = pcre_exec(
      re,              /* the compiled pattern */
      NULL,            /* no extra data - we didn't study the pattern */
      matched,         /* the subject string */
      strlen(matched), /* the length of the subject */
      0,               /* start at offset 0 in the subject */
      0,               /* default options */
      ovector,         /* output vector for substring information */
      OVECCOUNT);      /* number of elements in the output vector */

  free(matched);
  free(rs);
  return (rc >= 0) ? 
    make_Coq_Init_Datatypes_bool_true() : 
    make_Coq_Init_Datatypes_bool_false();
}


value bool_to_value(_Bool b) {
  if(b)
    return make_Coq_Init_Datatypes_bool_true();
  else
    return make_Coq_Init_Datatypes_bool_false();
}

value char_to_value(struct thread_info *tinfo, char c) {
  value v[8];
  for(unsigned int i = 0; i < 8; i++) {
    v[i] = bool_to_value(c & (1 << i));
  }
  return alloc_make_Coq_Strings_Ascii_ascii_Ascii(tinfo, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
}

value string_to_value(struct thread_info *tinfo, char *s) {
  value temp = make_Coq_Strings_String_string_EmptyString();
  for (unsigned int i = strlen(s); 0 < i; i--) {
    value c = char_to_value(tinfo, s[i-1]);
    temp = alloc_make_Coq_Strings_String_string_String(tinfo, c, temp);
  }
  return temp;
}

value rgx_exec(struct thread_info *tinfo, value r, value str) {
  int OVECCOUNT = 20;
  pcre *re;
  const char *error;
  int erroffset;
  int ovector[OVECCOUNT];
  int rc;

  size_t rs_size = regex_string_size(r);
  char *rs = (char *) malloc(rs_size * sizeof(char));
  regex_to_string(r, rs);
  char *matched = value_to_string(str);

  re = pcre_compile(
      rs,         /* the pattern */
      0,          /* default options */
      &error,     /* for error message */
      &erroffset, /* for error offset */
      NULL);      /* use default character table */

  if (! re) {
    exit(1);
  }

  rc = pcre_exec(
      re,              /* the compiled pattern */
      NULL,            /* no extra data - we didn't study the pattern */
      matched,         /* the subject string */
      strlen(matched), /* the length of the subject */
      0,               /* start at offset 0 in the subject */
      0,               /* default options */
      ovector,         /* output vector for substring information */
      OVECCOUNT);      /* number of elements in the output vector */

  value result;
  if(rc >= 0) {
    int limit = MIN(OVECCOUNT, rc * 2) - 2;
    value list = make_Coq_Init_Datatypes_list_nil();
    for(int i = limit; 0 <= i; i = i - 2) {
      char *start = matched + ovector[i];
      int length = ovector[i + 1] - ovector[i];
      char *new = (char *) malloc(length * sizeof(char));
      strncpy(new, start, length);
      value sv = string_to_value(tinfo, new);
      memset(new, 0, length);
      free(new);
      list = alloc_make_Coq_Init_Datatypes_list_cons(tinfo, sv, list);
    }
    result = alloc_make_Coq_Init_Datatypes_option_Some(tinfo, list);
  } else {
    result = make_Coq_Init_Datatypes_option_None();
  }
  free(matched);
  free(rs);
  return result;
}

/* Main */
extern void print_Coq_Strings_String_string(value v);

int main(int argc, char *argv[]) {
  value clo;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;

  tinfo = make_tinfo();
  start = clock();

  // Run Coq program
  clo = body(tinfo);
  end = clock();

  // Types are dummy values
  value regex_ffi = 
    alloc_make_CertiCoq_Benchmarks_regex_regex_RegexFFI_Build_RegexFFI(
        tinfo,
        rgx_test_clo,
        rgx_exec_clo);

  value v = call(tinfo, clo, regex_ffi);

  // if program is using the exec function:
  value list;
  char *s;
  switch(get_Coq_Init_Datatypes_option_tag(v)) {
    case 0:
      list = *((value *) v);
      puts("Matched!");
      int i = 0;
      while (get_Coq_Init_Datatypes_list_tag(list) != 0) {
        s = value_to_string(*((value *) list + 0));
        printf("Part #%d is %s\n", i, s);
        free(s);
        list = *((value *) list + 1);
        i++;
      }
      break;
    case 1:
      puts("No match found.");
      break;
  }

  // if program is using the test function:
  /* print_Coq_Init_Datatypes_bool(v); */

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("\nTime taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
