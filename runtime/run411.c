#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <sys/resource.h>
#include <time.h>

extern int _c0_main();
const int stack_limit = 8838608;

/* The main function, which calls _c0_main */
int main() {
  /* Set stack limit. */
  struct rlimit rlimit = { .rlim_cur = stack_limit, .rlim_max = stack_limit };
  if (setrlimit(RLIMIT_STACK, &rlimit) < 0) {
    printf("ERROR: rlimit failed in run411.c/main\n");
    exit(1);
  }

  printf("%d\n", _c0_main());
  exit(0);
}

/* Implementation of the 15411 library (used in L3 and L4) */

typedef int c0_float;
typedef int c0_bool;

union float_or_int {
  int as_int;
  float as_float;
};

typedef union float_or_int float_or_int;

c0_float fadd(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float + y.as_float;
  return z.as_int;
}

c0_float fsub(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float - y.as_float;
  return z.as_int;
}

c0_float fmul(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float * y.as_float;
  return z.as_int;
}

c0_float fdiv(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  float_or_int z; z.as_float = x.as_float / y.as_float;
  return z.as_int;
}

c0_bool fless(c0_float a, c0_float b) {
  float_or_int x; x.as_int = a;
  float_or_int y; y.as_int = b;
  return x.as_float < y.as_float ? 1 : 0;
}

c0_float itof(int a) {
  float_or_int x; x.as_float = (float)a;
  return x.as_int;
}

int ftoi(c0_float a) {
  float_or_int x; x.as_int = a;
  return (int)x.as_float;
}

typedef struct dub *c0_double;

union double_or_ptr {
  struct dub *as_ptr;
  double as_double;
};

typedef union double_or_ptr double_or_ptr;

c0_double dadd(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double + y.as_double;
  return z.as_ptr;
}

c0_double dsub(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double - y.as_double;
  return z.as_ptr;
}

c0_double dmul(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double * y.as_double;
  return z.as_ptr;
}

c0_double ddiv(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  double_or_ptr z; z.as_double = x.as_double / y.as_double;
  return z.as_ptr;
}

c0_bool dless(c0_double a, c0_double b) {
  double_or_ptr x; x.as_ptr = a;
  double_or_ptr y; y.as_ptr = b;
  return x.as_double < y.as_double;
}

c0_double itod(int a) {
  double_or_ptr x; x.as_double = (float)a;
  return x.as_ptr;
}

int dtoi(c0_double a) {
  double_or_ptr x; x.as_ptr = a;
  return (int)x.as_double;
}

int print_dub(c0_double a) {
  double_or_ptr x; x.as_ptr = a;
  fprintf(stderr, "%g\n", x.as_double);
  return 0;
}

int print_fpt(c0_float a) {
  float_or_int x; x.as_int = a;
  fprintf(stderr, "%g\n", x.as_float);
  return 0;
}

int print_int(int n) {
  fprintf(stderr, "%d\n", n);
  return 0;
}

int print_hex(int n) {
  fprintf(stderr, "0x%08X\n", n);
  return 0;
}


/* Common runtime implementation for C0 libraries */

void raise_msg(int signal, const char* msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(signal);
}

void c0_abort(const char *reason) {
  raise_msg(SIGABRT, reason);
}

void c0_abort_mem(const char *reason) {
  raise_msg(SIGUSR2, reason);
}

void _c0_assert(bool b) { 
  if (!b) { 
    c0_abort("assert.");
  }
}

void* c0_alloc(size_t elt_size) {
  // Require non-zero allocation so that alloc acts as a gensym
  if (elt_size == 0) elt_size = 1;
  void *p = calloc(1, elt_size);
  if (p == NULL) c0_abort_mem("allocation failed");
  return (void *)p;
}

void* c0_alloc_array(size_t elemsize, int elemcount) {
  /* test for overflow, somehow? */
  if (elemcount < 0) c0_abort_mem("array size cannot be negative");
  if (elemsize > 0 && elemcount > ((1<<30)-8)/elemsize)
    c0_abort_mem("array size too large");

  void** p = calloc(1, sizeof(void*) + elemcount*elemsize);

  /* initialize number of elements */
  *(int*)p = elemcount;

  return p+1; 
}

int length(void **A) {
  if (!A) return 0;

  /* Obtain the address one pointer-size to the left of A */
  void **B = A - 1; 
  return *(int*)B;
}


/* Implementation of the string library */

int string_length(char *str) {
  return str ? strlen(str) : 0;
}

int string_compare(char *a, char *b) {
  char* astr = a ? (char*)a : "";
  char* bstr = b ? (char*)b : "";
  int res = strcmp(astr,bstr);
  return (res < 0) ? -1 : ((res > 0) ? 1 : 0);
}

bool string_equal(char *a, char *b) {
  return 0 == string_compare(a, b);
}

char string_charat(char *s, int idx) {
  int len = string_length(s);
  if (!(0 <= idx && idx < len)) c0_abort("string_charat: index out of bounds");
  return s[idx];
}

char *string_join(char *a, char *b) {
  if (!a) return b;
  if (!b) return a;

  char *c = c0_alloc(strlen((char*)a) + strlen((char*)b) + 1);
  strcpy(c, a);
  strcat(c, b);
  return c;
}

char *string_frombool(bool b) {
  return b ? "true" : "false";
}

char *string_fromchar(char c) {
  char *buf = c0_alloc(2);
  if (!c) c0_abort("string_fromchar: cannot accept the null character");
  buf[0] = c;
  buf[1] = '\0';
  return buf;
}

bool string_terminated(void* A, int n) {
  int i;
  int len = length(A);
  if (!(0 <= n && n <= len)) c0_abort("string_termianted: out of bounds");
  for (i = 0; i < n; i++) {
    if ('\0' == ((char*)A)[i]) return true;
  }
  return false;
}

void *string_to_chararray(char *s) {
  int len = string_length(s);
  char *buf = c0_alloc_array(1, len+1);
  if (s) strcpy(buf, s);
  return buf;
}

char *string_from_chararray(void *A) {
  int len = length(A);
  if (!string_terminated(A, len))
    c0_abort("string_from_chararray: not '\0'-terminated");
  char *buf = c0_alloc(1+len);
  strcpy(buf, A);
  return buf;
}

int char_ord(char c) {
  return (int)c;
}

char char_chr(int n) {
  if (0 > n || n > 127) c0_abort("character outside ASCII range (0..127)");
  return (char)n;
}

/* Implementation of the rand library. */

int rand() {
    srandom(time(NULL));
    return random();
}

// Return a random number in the range [lo, hi] (inclusive on both ends)
int rand_range(int lo, int hi) {
    return (rand() % (hi - lo + 1)) + lo;
}
