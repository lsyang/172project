/**
 * Copyright (c) 2014 MIT License by 6.172 Staff
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 **/

/**************************************************************************
 * The files SIEVE.{H,C} declare and define the SIEVE_T data type,
 * which implements a sieve.
 *
 * A sieve is conceptually an array P where each entry represents an
 * integer in a range.  A sieve for the interval [0,n), for example,
 * is an array P of n entries where entry P[i] is 1 if i is prime and
 * 0 otherwise.  More generally, a sieve representing the range [l, h)
 * is an array P of h-l elements where P[i] is 1 if l+i is prime and 0
 * otherwise.
 *
 * See the documentation in SEGSIEVE.{H,C} for more on how the sieve
 * data structure is used to find primes in an interval.
 *************************************************************************/

#ifndef INCLUDED_SIEVE_DOT_H
#define INCLUDED_SIEVE_DOT_H

#include <inttypes.h>
#include <stdbool.h>
#include <stdlib.h>
#include <tbassert.h>

#define BASE 8

/**************************************************************************
 * Definition of SIEVE_T type.
 *************************************************************************/

// The SIEVE_T struct consists of an integer LENGTH followed by an
// array PRIMES of (length/8) 8-bits-integers. Each 8-bits-integer
// represents 8 booleans. If SIEVE is a variable of type
// SIEVE_T that represents a sieve for the interval [l,h), then
// SIEVE.LENGTH = h-l and (I % BASE)th bit of SIEVE.PRIMES[I \ BASE]
// 8-bits-integer is 1 if integer l+I is prime and 0 otherwise.

typedef struct sieve_t {
  int64_t length;
  uint_fast8_t primes[0];
} sieve_t;

/**************************************************************************
 * Methods on the SIEVE_T type
 *************************************************************************/

// Create a SIEVE_T structure of LENGTH elements.  Returns a pointer
// to the newly created SIEVE_T.
//
//   LENGTH -- The number of elements in the SIEVE being created.
//

static inline sieve_t* create_sieve(int64_t length) {
  tbassert(length > 0,
           "bad length %ld\n", length);
  int64_t bools_size = ((int64_t) length/BASE) + (length % BASE != 0);
  sieve_t *sieve = (sieve_t*) malloc(sizeof(sieve_t) +
                                    bools_size * sizeof(uint_fast8_t));
  /* tbassert(NULL != sieve, "malloc failed.\n"); */
  if (NULL != sieve) {
    sieve->length = length;
  }
  return sieve;
}

// Free the SIEVE_T structure.
//
//   SIEVE -- the SIEVE_T structure to free.
//
static inline void destroy_sieve(sieve_t *sieve) {
  free(sieve);
}

// Initialize the SIEVE_T structure such that all numbers are marked
// as prime.
//
//   SIEVE -- Pointer to the SIEVE_T structure to initialize.
//
static inline void init_sieve(sieve_t *sieve, int64_t length) {
  // Initially, all entries in SIEVE are marked as representing a
  // prime.

  int64_t remains = length % BASE;
  length = length / BASE;

  for (int64_t i = 0; i < length; ++i) {
    sieve->primes[i] = ~0;
  }
  if (remains != 0) {
    sieve->primes[length] = ((uint_fast8_t) 1 << remains) - 1;
  }
}

// Initialize the SIEVE_T structure such that all odd bits are marked as composites.
//
//   SIEVE -- Pointer to the SIEVE_T structure to initialize.
//
// example 10101010
static inline void init_sieve_with_odd_bits_off(sieve_t *sieve, int64_t length) {
  int64_t remains = length % BASE;
  length = length / BASE;

  for (int64_t i = 0; i < length; ++i) {
    // all even bits are marked as primes
    // 170 = 10101010
    sieve->primes[i] = 170;
  }
  if (remains != 0) {
    sieve->primes[length] = 170 & (((uint_fast8_t) 1 << remains) - 1);
  }
}

// Initialize the SIEVE_T structure such that all even bits are marked as composites.
//
//   SIEVE -- Pointer to the SIEVE_T structure to initialize.
//
// example 01010101
static inline void init_sieve_with_even_bits_off(sieve_t *sieve, int64_t length) {
  int64_t remains = length % BASE;
  length = length / BASE;

  for (int64_t i = 0; i < length; ++i) {
    // all even bits are marked as primes
    // 170 = 10101010
    sieve->primes[i] = 85;
  }
  if (remains != 0) {
    sieve->primes[length] = 85 & (((uint_fast8_t) 1 << remains) - 1);
  }
}

// Mark index I in SIEVE as composite.
//
//   SIEVE -- The target SIEVE_T to update.
//
//   I -- Index in SIEVE to mark as composite.
//
static inline void mark_composite(sieve_t *sieve, int64_t i) {
  tbassert(i >= 0 && i < sieve->length,
           "Invalid index %"PRId64".\n", i);
  // position of uint_fast8_t inside sieve->primes that stores boolean i
  int64_t pos = i / BASE;
  // position of boolean i inside this uint_fast8_t
  int64_t remain = i % BASE;
  // set that bit off
  sieve->primes[pos] &= ~((uint_fast8_t) 1 << remain);
}

// Mark index I in SIEVE as prime.
//
//   SIEVE -- The target SIEVE_T to update.
//
//   I -- Index in SIEVE to mark as prime.
//
static inline void mark_prime(sieve_t *sieve, int64_t i) {
  tbassert(i >= 0 && i < sieve->length,
           "Invalid index %"PRId64".\n", i);
  // position of uint_fast8_t inside sieve->primes that stores boolean i
  int64_t pos = i / BASE;
  // position of boolean i inside this uint_fast8_t
  int64_t remain = i % BASE;
  // set that bit on
  sieve->primes[pos] |= ((uint_fast8_t) 1 << remain);
}

// Returns whether index I corresponds to a prime.
//
//   SIEVE -- The target SIEVE_T to examine.
//
//   I -- The index to check for primality.
//
static inline bool prime_p(const sieve_t *sieve, int64_t i) {
  tbassert(i >= 0 && i < sieve->length,
           "Invalid index %"PRId64".\n", i);
  // position of uint_fast8_t inside sieve->primes that stores boolean i
  int64_t pos = i / BASE;
  // position of boolean i inside this int64_t
  int64_t remain = i % BASE;
  return sieve->primes[pos] & ((uint_fast8_t) 1 << remain);
}

#endif  // INCLUDED_SIEVE_DOT_H
