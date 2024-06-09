/*
   american fuzzy lop++ - sample argv fuzzing wrapper
   ------------------------------------------------

   Originally written by Michal Zalewski

   Copyright 2015 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This file shows a simple way to fuzz command-line parameters with stock
   afl-fuzz. To use, add:

   #include "/path/to/argv-fuzz-inl.h"

   ...to the file containing main(), ideally placing it after all the
   standard includes. Next, put AFL_INIT_ARGV(); near the very beginning of
   main().

   This will cause the program to read NUL-delimited input from stdin and
   put it in argv[]. Two subsequent NULs terminate the array. Empty
   params are encoded as a lone 0x02. Lone 0x02 can't be generated, but
   that shouldn't matter in real life.

   If you would like to always preserve argv[0], use this instead:
   AFL_INIT_SET0("prog_name");

*/

#ifndef _HAVE_ARGV_FUZZ_INL
#define _HAVE_ARGV_FUZZ_INL

#include <ctype.h>
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>

#define AFL_INIT_ARGV()          \
  do {                           \
                                 \
    argv = afl_init_argv(&argc, argv); \
                                 \
  } while (0)

#define AFL_INIT_SET0(_p)        \
  do {                           \
                                 \
    argv = afl_init_argv(&argc); \
    argv[0] = (_p);              \
    if (!argc) argc = 1;         \
                                 \
  } while (0)

#define MAX_CMDLINE_LEN 100000
#define MAX_CMDLINE_PAR 50000

static char **afl_init_argv(int *argc, char** argv) {

  static char  in_buf[MAX_CMDLINE_LEN];
  static char *ret[MAX_CMDLINE_PAR];

  /*
  FILE *old_file = fopen("old_argv.txt", "w");
  for (int i = 0; i < *argc; i++) {
    fprintf(old_file, "old argv[%d]: %s\n", i, argv[i]);
  }
  fclose(old_file);
  */
  char *ptr = in_buf;
  int   rc = 0;

  int fd = open(argv[1], O_RDONLY);

  if (read(fd, in_buf, MAX_CMDLINE_LEN - 2) < 0) {}
  /*
  FILE* buf_file = fopen("buf_file.txt", "w");
  fprintf(buf_file, "%s\n", in_buf);
  fclose(buf_file);
  */
  ret[rc] = argv[0];
  ++rc;

  while (*ptr && rc < MAX_CMDLINE_PAR) {

    while (*ptr && isspace(*ptr)) ptr++;
    if (!(*ptr)) break;

    ret[rc] = ptr;

    rc++;

    while (*ptr && !isspace(*ptr))
      ptr++;
    *ptr = '\0';
    ptr++;

  }

   if (*argc > 2) {
    for (int i = 2; i < *argc; i++) {
      ret[rc++] = argv[i];
    }
  }

  *argc = rc;
  /*
  FILE *new_file = fopen("new_argv.txt", "w");
  for (int i = 0; i < rc; i++) {
    fprintf(new_file, "argv[%d]: %s\n", i, ret[i]);
  }
  fclose(new_file);
 */

  return ret;

}

#undef MAX_CMDLINE_LEN
#undef MAX_CMDLINE_PAR

#endif                                              /* !_HAVE_ARGV_FUZZ_INL */

