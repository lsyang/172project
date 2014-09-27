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
 * The files COUNT_PRIMES.{H,C} implement the
 * COUNT_PRIMES_IN_INTERVAL() method using a _segmented prime sieve_
 * algorithm, specifically, a segmented Sieve of Eratosthenes.
 *
 * To understand how a segmented sieve algorithm works, let us first
 * see how a basic prime sieve works.  Consider finding all primes in
 * the interval [0, n).  First, a sieve S of length n -- conceptually,
 * an array S of n entries -- is created to represent the integers in
 * [0, n), and all entries S[i] in the sieve are initialized to 1.
 * Entries S[0] and S[1] are then set to 0, indicating that 0 and 1
 * are composite, and then the remaining entries S[i] of the sieve are
 * scanned from i = 2 to n.  As this scan progresses, if the scan
 * finds that S[i] = 1, then i is prime, and for each multiple k*i in
 * [2*i, n), entry P[k*i] is set to 0, thereby marking k*i as
 * composite.  At the end of the scan, the only entries in S[i] equal
 * to 1 are those for which i is prime.
 *
 * The COUNT_PRIMES_IN_INTERVAL() method defined here implements a
 * segmented sieve algorithm, which extends the basic prime sieve
 * algorithm to reduce space usage.  To describe the
 * COUNT_PRIMES_IN_INTERVAL() method, suppose that
 * COUNT_PRIMES_IN_INTERVAL() is invoked to find all primes in an
 * interval [START, START+LENGTH) of nonnegative numbers less than
 * 2^63.  The MAX_SIEVE_LENGTH constant stores the maximum size of a
 * sieve that COUNT_PRIMES_IN_INTERVAL() will allocate, and for
 * didactic simplicity, let us assume that LENGTH >= MAX_SIEVE_LENGTH
 * > \sqrt{h}.
 *
 * -) First, COUNT_PRIMES_IN_INTERVAL() calls the FIND_SMALL_PRIMES()
 * helper, which executes a basic prime sieve algorithm to find all
 * primes in [0, 1.42 * 2^31).  The resulting SMALL_PRIMES sieve
 * countains all of the primes needed to sieve [START, START+LENGTH),
 * because any composite value in [START, START+LENGTH) where
 * START+LENGTH < 2^63 is divisible by some prime in [0,
 * \sqrt{START+LENGTH}) \subset [0, 1.42 * 2^31).
 *
 * -) Next, COUNT_PRIMES_IN_INTERVAL() calls the
 * COUNT_PRIMES_IN_INTERVAL_HELPER() method to sieve the interval
 * [START, START+MAX_SIEVE_LENGTH) as follows.
 *
 * --) To sieve [START, START+MAX_SIEVE_LENGTH),
 * COUNT_PRIMES_IN_INTERVAL_HELPER() first creates the LARGE_PRIMES
 * sieve to represent [START, START+MAX_SIEVE_LENGTH), i.e., a sieve
 * of length MAX_SIEVE_LENGTH whose Ith entry ultimately records the
 * primality of I+START.
 *
 * --) COUNT_PRIMES_IN_INTERVAL_HELPER() then considers each prime P
 * in SMALL_PRIMES and markes each multiple of P in [START,
 * START+MAX_SIEVE_LENGTH) that is larger than P and smaller than
 * START+MAX_SIEVE_LENGTH as composite.  Once all primes in
 * SMALL_PRIMES have been evaluated, all sieve entries representing
 * composite values in [START, START+MAX_SIEVE_LENGTH) have been
 * marked as composite.
 *
 * --) COUNT_PRIMES_IN_INTERVAL_HELPER() then scans LARGE_PRIMES to
 * count the number of primes in [START, START+MAX_SIEVE_LENGTH) and
 * returns this count to COUNT_PRIMES_IN_INTERVAL().
 *
 * -) COUNT_PRIMES_IN_INTERVAL() then updates START and LENGTH to
 * evaluate the next unevaluated segment of [START, START+LENGTH) of
 * length at most MAX_SIEVE_LENGTH and repeats the process.
 *
 * These methods use the SIEVE_T data type defined in SIEVE.H, which
 * implements a sieve data structure.  See the documentation in
 * SIEVE.H for more on the sieve data struture.
 *************************************************************************/

/**************************************************************************
 * WARNING: This code can allocate nearly 4GB of memory at once.
 * Errors might occur if this code is run on a machine with
 * insufficient memory.
 *************************************************************************/

#include "./count_primes.h"

#include <stdio.h>
#include <math.h>

#include "./sieve.h"
#include "./trialdiv.h"

#define min(a, b) (a < b) ? a : b
#define threshold 1000000000000000LL

const int64_t MAX_SIEVE_LENGTH_SMALL = 10000000;
const int64_t MAX_SIEVE_LENGTH_BIG = (int64_t)1 << 30;
int64_t *a_small_primes;
int64_t n_small_primes = 0;

/*************************************************************************
 * Helper methods
 *************************************************************************/

// Helper method that finds all "small" primes -- primes in [0, sqrt(max_consider)].
static inline void find_small_primes(int64_t max_consider) {
  int64_t upper_bound = (int64_t)(sqrt(max_consider)) + 1L;
  int64_t sqrt_upper_bound = (int64_t)(sqrt(upper_bound)) + 2L;
  sieve_t *sieve = create_sieve(upper_bound+10);

  a_small_primes = (int64_t*) malloc(upper_bound * sizeof(int64_t));
  int64_t *it = a_small_primes;

  init_sieve(sieve);

  mark_composite(sieve, 0);
  mark_composite(sieve, 1);

  // Scan the entries of the sieve from 3 to UPPER_BOUND
  int64_t i = 5;
  for (; i < sqrt_upper_bound; i += 4) {
    // Skip any I marked as composite
    if (prime_p(sieve, i)) {
      n_small_primes++;
      *(it ++) = i;
      for (int64_t j = i; i * j < sqrt_upper_bound; j += 2) {
        mark_composite(sieve, i * j);
      }
    }
    i += 2;
    if (prime_p(sieve, i)) {
      n_small_primes++;
      *(it ++) = i;
      for (int64_t j = i; i * j < sqrt_upper_bound; j += 2) {
        mark_composite(sieve, i * j);
      }
    }
  }

  int64_t * it_sqrt = it;
  int64_t prev_i = i;
  while (i < upper_bound) {
    int64_t next_stop = min(upper_bound, i + MAX_SIEVE_LENGTH_SMALL);
    for (int64_t * itt = a_small_primes; itt != it_sqrt; ++itt) {
      int64_t p = *itt;
      int64_t st = (i / p) * p + p;
      if (!(st & 1)) {
        st += p;
      }
      p += p;
      for (; st < next_stop; st += p) {
        mark_composite(sieve, st);
      }
    }
    i = next_stop;
  }

  i = prev_i;
  if (i%3 == 1) {
    if (prime_p(sieve, i)) {
      n_small_primes++;
      *(it ++) = i;
    }
    i += 4;
  }
  for (; i < upper_bound; i += 4) {
    if (prime_p(sieve, i)) {
      n_small_primes++;
      *(it ++) = i;
    }
    i += 2;
    if (prime_p(sieve, i)) {
      n_small_primes++;
      *(it ++) = i;
    }
  }

  // We do not need sieve anymore.
  destroy_sieve(sieve);
}

// Helper function for COUNT_PRIMES_IN_INTERVAL() to count the number
// of primes in [START, START+LENGTH) where 0 < LENGTH <=
// MAX_SIEVE_LENGTH.  Returns the number of primes in [START,
// START+LENGTH).
//
//   START -- The low endpoint of the interval.
//
//   LENGTH -- The length of the interval.
//
//   SMALL_PRIMES -- Sieve recording all necessary primes.
//
static int64_t count_primes_in_interval_helper(int64_t start, int64_t length) {
  int64_t num_primes = 0;

  // Create LARGE_PRIMES structures to record the primes in
  // [START,START+LENGTH), where index I in LARGE_PRIMES corresponds
  // to the integer LOW+I.
  sieve_t *large_primes = create_sieve(length+6);

  init_sieve(large_primes);

  mark_composite(large_primes, length+1);
  mark_composite(large_primes, length+3);
  mark_composite(large_primes, length+5);

  // Scan all of the potentially prime entries in the SMALL_PRIMES
  // sieve.
  int64_t * it = a_small_primes;
  int64_t * it_end = a_small_primes + n_small_primes;
  while (it != it_end) {
    int64_t p = *(it ++);

    // At this point, P is a prime.
    /* DEBUG_EPRINTF("p = %ld\n", p); */

    // Find index KP_INDEX of smallest multiple of <p> in range
    // [START,START+LENGTH).
    int64_t kp_index = start % p;
    if (0 != kp_index) {
      kp_index = p - kp_index;
    }
    if (start + kp_index == p) {
      kp_index += p;
    }

    // if kp_index is even, then make it odd!
    kp_index += p * !((kp_index & 1) ^ (start & 1));

    // p is now an even number.
    p += p;

    /* DEBUG_EPRINTF("kp_index = %"PRId64"\n", kp_index); */

    // Mark all multiples of P in [KP_INDEX, KP_INDEX+LENGTH) as
    // composite.
    for ( ; kp_index < length; kp_index += p) {
      mark_composite(large_primes, kp_index);
    }
  }

  // Count number of primes in LARGE_PRIMES.
  num_primes = 0;
  int64_t i = !(start & 1);
  int64_t j = (start + i) % 3;

  if (j == 0) {
    i += 2;
  } else if (j == 1) {
    if (prime_p(large_primes, i)) {
      ++num_primes;
    }
    i += 4;
  }

  for (; i < length; i += 4) {
    if (prime_p(large_primes, i)) {
      ++num_primes;
    }
    i += 2;
    if (prime_p(large_primes, i)) {
      ++num_primes;
    }
  }

  // Free LARGE_PRIMES structure
  destroy_sieve(large_primes);

  return num_primes;
}

/*************************************************************************
 * Definitions for methods in header file.                               
 *************************************************************************/

int64_t count_primes_in_interval(int64_t start, int64_t length) {
  // Initialize NUM_PRIMES
  int64_t num_primes = 0;

  // Return 0 primes for nonpositive-length intervals.
  if (length <= 0) {
    return 0;
  }

  // Return 0 primes for intervals whose high endpoint is at most 2.
  // Because we treat all negative numbers as composite, there are no
  // primes less than 2.
  if (start + length <= 2) {
    return 0;
  }

  // Ensure that the smallest value of START is 2.
  if (start < 2) {
    length -= 2 - start;
    start = 2;
  }

  // Make sure start always be odd
  if (!(start & 1)) {
    if (start == 2) {
      num_primes++;
    }
    start++;
    length--;
  }

  // Make sure start is more than 3
  if (start == 3 && length != 0) {
    num_primes++;
    if (length <= 2) {
      length = 0;
    } else {
      start += 2;
      length -= 2;
    }
  }

  // The variable showing the maximum integer we will consider.
  int64_t end = start + length;

  // Create SMALL_PRIMES structure to record the small primes
  find_small_primes(end);

  // Choose max_interval length based on the input size.
  int64_t max_interval = (end <= threshold) ? MAX_SIEVE_LENGTH_SMALL : MAX_SIEVE_LENGTH_BIG;

  // Segment the interval [START, START+LENGTH) into subintervals no
  // longer than MAX_SIEVE_LENGTH.
  while (length > max_interval) {
    // Count the number of primes in this segment, and add this count
    // to NUM_PRIMES.
    num_primes += count_primes_in_interval_helper(start, max_interval);
    // Update START and LENGTH to handle the next segment
    start += max_interval;
    length -= max_interval;
  }
  // Count the number of primes in the final segment, and add the
  // count to NUM_PRIMES.
  if (length > 0) {
    num_primes += count_primes_in_interval_helper(start, length);
  }

  // Free SMALL_PRIMES.
  free(a_small_primes);

  return num_primes;
}
