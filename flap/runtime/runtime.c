#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int equal_string(const char* s1, const char* s2) {
  return (strcmp (s1, s2) == 0 ? 1 : 0);
}

int equal_char(char c1, char c2) {
  return (c1 == c2 ? 1 : 0);
}

void print_string(const char* s) {
  printf("%s", s);
}

void print_int(int64_t n) {
  //fprintf(stderr, "Students! This is your job!\n");
  printf("%ld", n);
}

void observe_int(int64_t n) {
  print_int(n);
}

int add_eight_int(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g, int64_t h) {
  int sum = a+b+c+d+e+f+g+h;
  observe_int(sum);
  return sum;
}

intptr_t* allocate_block (int64_t n) {
  return (intptr_t*)malloc (n * sizeof (int64_t));
}

intptr_t read_block (intptr_t* block, int64_t n) {
  return block[n];
}

int64_t write_block (intptr_t* block, int64_t n, intptr_t v) {
  block[n] = v;
  return 0;
}
