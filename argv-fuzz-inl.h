#ifndef _HAVE_ARGV_FUZZ_INL
#define _HAVE_ARGV_FUZZ_INL

#include <unistd.h>
#include <ctype.h>
#include <fcntl.h>

#define AFL_INIT_ARGV() do { \
    int fd = open(argv[1], O_RDONLY); \
    argv = afl_init_argv(&argc, fd); \
    close(fd); \
  } while (0)

#define AFL_INIT_SET0(_p) do { \
    argv = afl_init_argv(&argc); \
    argv[0] = (_p); \
    if (!argc) argc = 1; \
  } while (0)

#define MAX_CMDLINE_LEN 100000
#define MAX_CMDLINE_PAR 1000

static char** afl_init_argv(int* argc, int fd) {

  static char  in_buf[MAX_CMDLINE_LEN];
  static char* ret[MAX_CMDLINE_PAR];

  char* ptr = in_buf;
  int   rc  = 1; /* start after argv[0] */

  if (read(fd, in_buf, MAX_CMDLINE_LEN - 2) < 0);

  while (*ptr) {

    ret[rc] = ptr;

    /* insert '\0' at the end of ret[rc] on first space-sym */
    while (*ptr && !isspace(*ptr)) ptr++;
    *ptr = '\0';
    ptr++;

    /* skip more space-syms */
    while (*ptr && isspace(*ptr)) ptr++;

    rc++;
  }

  *argc = rc;

  return ret;

}

#undef MAX_CMDLINE_LEN
#undef MAX_CMDLINE_PAR

#endif /* !_HAVE_ARGV_FUZZ_INL */