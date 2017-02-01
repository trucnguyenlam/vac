/* 24.12.2008 last modification: 26.06.2013
Copyright (c) 2008-2013 by Siegfried Koepf

This file is distributed under the terms of the GNU General Public License
version 3 as published by the Free Software Foundation.
For information on usage and redistribution and for a disclaimer of all
warranties, see the file COPYING in this distribution.

k-combinations without repetition in lexicographic order

Algorithm by Siegfried Koepf, inspired by Donald Knuth and many others

Functions:
  int gen_comb_norep_lex_init(unsigned char *vector, const unsigned char n, const unsigned char k)
    Test for special cases
    Initialization of vector
    Possible return values are: GEN_ERROR, GEN_EMPTY, GEN_NEXT

  int gen_comb_norep_lex_next(unsigned char *vector, const unsigned char n, const unsigned char k)
    Transforms current figure in vector into its successor
    Possible return values are: GEN_NEXT, GEN_TERM

Arguments:
  unsigned char *vector; //pointer to the array where the current figure is stored
  const unsigned char n; //length of alphabet
  const unsigned char k; //length of figures

Usage and restrictions:
  Arguments and elements in vector are restricted to the interval (0, 255)
  Memory allocation for vector must be provided by the calling process
  k must be <= n

Cardinality:
  n! / ((n - k)! * k!) == Binomial(n, k)
*/

#include "_generate.h"

int gen_comb_norep_lex_init(unsigned char *vector, const unsigned char n, const unsigned char k)
{
  int j; //index

//test for special cases
  if (k > n)
    return (GEN_ERROR);

  if (k == 0)
    return (GEN_EMPTY);

//initialize: vector[0, ..., k - 1] are 0, ..., k - 1
  for (j = 0; j < k; j++)
    vector[j] = j;

  return (GEN_NEXT);
}

int gen_comb_norep_lex_next(unsigned char *vector, const unsigned char n, const unsigned char k)
{
  int j; //index

//easy case, increase rightmost element
  if (vector[k - 1] < n - 1)
  {
    vector[k - 1]++;
    return (GEN_NEXT);
  }

//find rightmost element to increase
  for (j = k - 2; j >= 0; j--)
    if (vector[j] < n - k + j)
      break;

//terminate if vector[0] == n - k
  if (j < 0)
    return (GEN_TERM);

//increase
  vector[j]++;

//set right-hand elements
  while (j < k - 1)
  {
    vector[j + 1] = vector[j] + 1;
    j++;
  }

  return (GEN_NEXT);
}
