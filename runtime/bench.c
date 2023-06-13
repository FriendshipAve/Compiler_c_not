/*******************************************************************
 *
 * bench.c - Benchmark run for 15-411 Compiler Design Lab 5 (optimization)
 *
 ********************************************************************/

#define _GNU_SOURCE
#include <sched.h>
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <getopt.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdbool.h>
#include <time.h>
#include <sys/resource.h>

#define MAXITERS 20        /* Max number of iterations of benchmarks */
#define KBEST 8
#define EPSILON 0.005          /* KBEST samples should be within EPSILON */

/* extern int _c0_main(); */    /* unused here */
extern void* _c0_init(int param);
extern void _c0_prepare(void* data, int param);
extern void _c0_run(void* data, int param);
extern int _c0_checksum(void* data, int param);

/*********************************/
/* Cycle counting infrastructure */
/*********************************/

/* Initialize the cycle counter */
static uint32_t cyc_hi = 0;
static uint32_t cyc_lo = 0;

/* Set *hi and *lo to the high and low order bits  of the cycle counter.
   Implementation requires assembly code to use the rdtsc instruction. */
void access_counter(uint32_t *hi, uint32_t *lo)
{
  asm __volatile__ ("xorl %%eax, %%eax; cpuid"
                    ::: "%rax", "%rbx", "%rcx", "%rdx");
  asm __volatile__ ("rdtsc"   /* Read cycle counter */
                    : "=a" (*lo), "=d" (*hi));
}

/* Record the current value of the cycle counter. */
void start_counter()
{
  access_counter(&cyc_hi, &cyc_lo);
}

uint64_t to64(uint32_t hi32, uint32_t lo32) {
  return (((uint64_t)hi32)<<32) + (uint64_t)lo32;
}

/* Return the number of cycles since the last call to start_counter. */
uint64_t get_counter()
{
  uint32_t ncyc_hi, ncyc_lo;
  uint64_t now, before;

  /* Get cycle counter */
  access_counter(&ncyc_hi, &ncyc_lo);
  now = to64(ncyc_hi, ncyc_lo);
  before = to64(cyc_hi, cyc_lo);
  return (now - before);
}

/*******************************/
/* Benchmarking infrastructure */
/*******************************/

/* Other globals */
static int debug_level = 0;

static uint64_t values[KBEST];
static int samplecount = 0;

static int add_sample(uint64_t val) {
  int pos = 0;
  if (samplecount < KBEST) {
    pos = samplecount;
    values[pos] = val;
  } else if (val < values[KBEST-1]) {
    pos = KBEST-1;
    values[pos] = val;
  }
  samplecount++;
  /* Insertion sort */
  while (pos > 0 && values[pos-1] > values[pos]) {
    uint64_t temp = values[pos-1];
    values[pos-1] = values[pos];
    values[pos] = temp;
    pos--;
  }

  return (samplecount >= KBEST
          && (1.0+EPSILON)*(double)values[0] >= (double)values[KBEST-1]);
}

/* Function prototypes */
void usage(char *progname);
void init_timeout(int timeout);
uint64_t time_run();


// This is _higher_ than the normal runtime's.
const int stack_limit = 8838608 * 4;

// Main routine
int main(int argc, char *argv[]) {
  char c;
  int i, j;
  void* data;
  int param;
  uint64_t cycles;

  // Set stack limit.
  struct rlimit rlimit = { .rlim_cur = stack_limit, .rlim_max = stack_limit };
  if (setrlimit(RLIMIT_STACK, &rlimit) < 0) {
    printf("ERROR: rlimit failed in bench.c/main\n");
    exit(1);
  }

  /* Initialization */
  
  debug_level = 0;
  param = 1000;
  int checksums = 0;            /* do not write checksums by default */
  int verify = 0;               /* do not verify, by default */
  int checksum = 0;

  /* parse command line args */
  while ((c = getopt(argc, argv, "hkd:n:x:")) != -1) {
    switch (c) {
    case 'd': /* debug level */
      debug_level = atoi(optarg);
      break;

    case 'k': /* checksums */
      checksums = 1;
      break;

    case 'h': /* print help message */
      usage(argv[0]);
      break;

    case 'n': /* parameter value */
      param = atoi(optarg);
      break;

    case 'x': /* checksum */
      verify = 1;
      checksum = atoi(optarg);
      break;

    default: /* unrecognized argument */
      usage(argv[0]);
    }
  }

#ifdef __linux__
  cpu_set_t s;
  CPU_ZERO(&s);
  CPU_SET(0, &s);

  if (sched_setaffinity(0, sizeof(s), &s) < 0) {
    perror("sched_setaffinity");
    exit(-1);
  }
#endif

  /* Initialize and touch the input data */
  samplecount = 0;

  /* One run to warm up cache */
  data = _c0_init(param);
  _c0_prepare(data, param);
  time_run(data, param);
  /* Timing runs */

  if (checksums) {
    /* compute and print checksum */
    printf("%d\n", _c0_checksum(data, param));
    exit(0);
  }

  if (verify != 0) {
    int chk = _c0_checksum(data, param);
    if (chk != checksum) {
      fprintf(stderr, "Checksum %d != %d\n", chk, checksum);
      exit(1);
    }
  }

  for (i = 0; i < MAXITERS; i++) {
    _c0_prepare(data, param);
    cycles = time_run(data, param);
    if (add_sample(cycles)) {
      i++; break;
    }
  }
  cycles = 0;
  for (j = 0; j < KBEST; j++) {
    cycles += values[j];
  }
  cycles /= KBEST;

  /* Print best score */
  if (debug_level >= 1) fprintf(stderr, "Iterations: %d\n", i);
  if (debug_level >= 1) fprintf(stderr, "Best cycles: %" PRIu64 "\n", values[0]);
  if (debug_level >= 1) fprintf(stderr, "%d-Best cycles: %" PRIu64 "\n", KBEST, cycles);
  printf("%" PRIu64 "\n", cycles);
  exit(0);
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

/*
 * time_run - Time a benchmark
 */
uint64_t time_run(void* data, int param) {
  uint64_t cycles;

  /* Time the function */
  /* no input, so no need to rewind */
  /* rewind(stdin); */
  start_counter();
  _c0_run(data, param);
  cycles = get_counter();
  if (debug_level >= 2) fprintf(stderr, "%" PRIu64 " cycles\n", cycles);
  return cycles;
}

/*
 * usage - print a usage message
 */
void usage(char *progname) {
  fprintf(stderr, "usage: %s [-hg]\n", progname);
  fprintf(stderr, "  -h        Print this message\n");
  fprintf(stderr, "  -k        Create checksums files\n");
  fprintf(stderr, "  -x <N>    Verify checksum = <N>\n");
  fprintf(stderr, "  -d <D>    Set debug level (default = 0)\n");
  fprintf(stderr, "  -n <N>    Set <N> as benchmark parameter (default = 1000)\n");
  exit(0);
}
