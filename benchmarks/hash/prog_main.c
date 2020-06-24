#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include "gc.h"

extern value body(struct thread_info *);
extern value args[];

extern struct thread_info;
extern unsigned int get_Coq_Strings_String_string_tag(value);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(value);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern value make_Coq_Init_Datatypes_unit_tt(void);
extern value make_Coq_Init_Datatypes_nat_O(void);
extern value make_Coq_Init_Datatypes_option_None(void);
extern value make_Coq_Strings_String_string_EmptyString(void);
extern value alloc_make_Coq_Strings_Ascii_ascii_Ascii(struct thread_info *, value, value, value, value, value, value, value, value);
extern value alloc_make_Coq_Strings_String_string_String(struct thread_info *, value, value);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
extern value alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, value);

extern value alloc_make_CertiCoq_Benchmarks_hash_hash_IO_Types_Build_IO_Types(struct thread_info *, value);
extern value alloc_make_CertiCoq_Benchmarks_hash_hash_IO_Impl_Build_IO_Impl(struct thread_info *, value, value);
extern value alloc_make_CertiCoq_Benchmarks_hash_hash_StringFFI_Build_StringFFI(struct thread_info *, value, value);
extern value alloc_make_CertiCoq_Benchmarks_hash_hash_Hash_Types_Build_Hash_Types(struct thread_info *, value);
extern value alloc_make_CertiCoq_Benchmarks_hash_hash_HashFFI_Build_HashFFI(struct thread_info *, value, value, value, value);

extern value call(struct thread_info *tinfo, value clos, value arg0);

extern value const io_ret_clo[2];
extern value const io_bind_clo[2];
extern value const print_string_clo[2];
extern value const scan_string_clo[2];
extern value const new_clo[2];
extern value const lookup_clo[2];
extern value const insert_clo[2];
extern value const delete_clo[2];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

value calls(struct thread_info* tinfo, value clos, unsigned int n, ...)
{
  value v = clos;
  va_list args;
  va_start(args, n);

  for(; n != 0; n--) {
    v = va_arg(args, value);
    clos = call(tinfo, clos, v);
  }
  va_end(args);
  return clos;
}

value io_ret(struct thread_info * tinfo, value sigma, value x) {
  return x;
}

value io_bind(struct thread_info * tinfo, value sigma, value tau, value x, value f) {
  call(tinfo, x, 1);
  // dereference to get the first thing in A * World
  value out = *((value *) tinfo->args[1]);
  calls(tinfo, f, 2, out, 1);
  return *((value *) tinfo->args[1]);
}

unsigned char ascii_to_char(value x) {
  unsigned char c = 0;
  for(unsigned int i = 0; i < 8; i++) {
    unsigned int tag = get_Coq_Init_Datatypes_bool_tag(*((value *) *((value *) x) + i));
    c += !tag << i;
  }
  return c;
}

value print_string(struct thread_info *tinfo, value s) {
  value temp = s;

  while(1) {
    unsigned int tag = get_Coq_Strings_String_string_tag(temp);
    if(tag == 1) {
      printf("%c", ascii_to_char(temp));
      temp = *((value *) temp + 1ULL);
    } else {
      break;
    }
  } 
  printf("\n");
  fflush(stdout);

  return make_Coq_Init_Datatypes_unit_tt();
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

value scan_string(struct thread_info *tinfo) { 
  char input[100];
  scanf("%s", input);

  value s = string_to_value(tinfo, input);
  return s;
}

value uint_to_nat(struct thread_info *tinfo, unsigned int num) {
  value n = make_Coq_Init_Datatypes_nat_O();
  for(unsigned int i = 0; i <= num; i++) {
    n = alloc_make_Coq_Init_Datatypes_nat_S(tinfo, n);
  }
  return n;
}

unsigned int nat_to_uint(value n) {
  value temp = n;
  unsigned int i = 0;

  while(1) {
    unsigned int tag = get_Coq_Init_Datatypes_nat_tag(temp);
    if(tag == 1) {
      i++;
      temp = *((value *) temp);
    } else {
      break;
    }
  } 
  return i;
}



// Hash table borrowed from
// https://www.cs.princeton.edu/~appel/vc/Hashfun.html
// with significant modifications to make it work on CertiCoq values
enum {SIZE = 109};

struct cell {
  value key;
  value val;
  struct cell *next;
};

struct hashtable {
  struct cell *buckets[SIZE];
};

struct hashtable *new_table (void) {
  int i;
  struct hashtable *p = (struct hashtable * )malloc(sizeof(struct hashtable));
  if (!p) exit(1);
  for (i=0; i<SIZE; i++) p->buckets[i]=NULL;
  return p;
}

struct cell *new_cell (value k, value v, struct cell *next) {
  struct cell *p = (struct cell * )malloc(sizeof(struct cell));
  if (!p) exit(1);
  p->key = k;
  p->val = v;
  p->next = next;
  return p;
}

value new(struct thread_info * tinfo, value sigma, value tau) {
  // the hashtable lives in C-land, 
  // we would have to do memory management for it later manually
  return (value) new_table();
}

value lookup(struct thread_info * tinfo, 
             value sigma, value tau, value eq_inst, value hashable_inst,
             value table, value key) {
  call(tinfo, *((value *) hashable_inst), key);
  unsigned int h = nat_to_uint(tinfo->args[1]); //possibly problematic
  unsigned int b = h % SIZE;
  struct cell *p = ((struct hashtable *) table)->buckets[b];
  while (p) {
    calls(tinfo, *((value *) eq_inst), 2, p->key, key);
    value cmp = tinfo->args[1]; //possibly problematic

    if (cmp == make_Coq_Init_Datatypes_bool_true())
      return alloc_make_Coq_Init_Datatypes_option_Some(tinfo, p->val);
    p=p->next;
  }
  return make_Coq_Init_Datatypes_option_None();
}

void insert_list(struct thread_info * tinfo, 
                  value eq_inst,
                  struct cell **r0, value key, value val) {
  struct cell *p, **r;
  for(r=r0; ; r=&p->next) {
    p = *r;
    if (!p) {
      *r = new_cell(key, val, NULL);
      return;
    }

    calls(tinfo, *((value *) eq_inst), 2, p->key, key);
    value cmp = tinfo->args[1]; //possibly problematic

    if (cmp == make_Coq_Init_Datatypes_bool_true()) {
      p->val = val;
      return;
    }
  }
}

value insert(struct thread_info * tinfo, 
             value sigma, value tau, value eq_inst, value hashable_inst,
             value table, value key, value val) {
  call(tinfo, *((value *) hashable_inst), key);
  unsigned int h = nat_to_uint(tinfo->args[1]); //possibly problematic
  unsigned int b = h % SIZE;
  insert_list(tinfo, eq_inst, & ((struct hashtable *) table)->buckets[b], key, val);
  return make_Coq_Init_Datatypes_unit_tt();
}

void delete_list(struct thread_info * tinfo, 
                  value eq_inst,
                  struct cell **r0, value key) {
  struct cell *p, **r;
  for(r=r0; ; r=&p->next) {
    p = *r;
    if (!p) { // key is not there so don't do anything
      return;
    }

    calls(tinfo, *((value *) eq_inst), 2, p->key, key);
    value cmp = tinfo->args[1]; //possibly problematic

    if (cmp == make_Coq_Init_Datatypes_bool_true()) {
      *r = p->next;
      free(p);
      return;
    }
  }
}

value delete(struct thread_info * tinfo, 
             value sigma, value tau, value eq_inst, value hashable_inst,
             value table, value key) {
  call(tinfo, *((value *) hashable_inst), key);
  unsigned int h = nat_to_uint(tinfo->args[1]); //possibly problematic
  unsigned int b = h % SIZE;
  delete_list(tinfo, eq_inst, & ((struct hashtable *) table)->buckets[b], key);
  return make_Coq_Init_Datatypes_unit_tt();
}

/* Main */
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
  value io_types = alloc_make_CertiCoq_Benchmarks_hash_hash_IO_Types_Build_IO_Types(tinfo, 1);

  value io_impl = alloc_make_CertiCoq_Benchmarks_hash_hash_IO_Impl_Build_IO_Impl(tinfo, io_ret_clo, io_bind_clo);

  value string_ffi = 
    alloc_make_CertiCoq_Benchmarks_hash_hash_StringFFI_Build_StringFFI(
        tinfo,
        print_string_clo,
        scan_string_clo);

  // Types are dummy values
  value hash_types = alloc_make_CertiCoq_Benchmarks_hash_hash_Hash_Types_Build_Hash_Types(tinfo, 1);

  // TODO these functions don't handle garbage collection yet.
  value hash_ffi = 
    alloc_make_CertiCoq_Benchmarks_hash_hash_HashFFI_Build_HashFFI(
        tinfo,
        new_clo,
        lookup_clo,
        insert_clo,
        delete_clo);

  // Worlds are dummy values in runtime
  value world = 1;

  value v = calls(tinfo, clo, 6, io_types, io_impl, string_ffi, hash_types, hash_ffi, world);

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("\nTime taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
