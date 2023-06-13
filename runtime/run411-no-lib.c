#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <sys/resource.h>

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
