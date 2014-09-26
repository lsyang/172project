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
#ifndef NDEBUG
#define NDEBUG
#endif  // NDEBUG
#include <tbassert.h>

#include "./sieve.h"
#include "./trialdiv.h"

// Maximum length of an interval represented by a SIEVE data
// structure.  Limiting MAX_SIEVE_LENGTH to 2^30 ensures that this program
// allocates at most ~5GB of physical memory.
const int64_t MAX_SIEVE_LENGTH = (int64_t)1 << 30;

// this static array is used to store temparary large array that is used in
// count_primes_in_interval_helper
static sieve_t *large_primes;

/*************************************************************************
 * Helper methods
 *************************************************************************/

static sieve_t* find_small_primes(int64_t power) {
  int64_t upper_bound = (int64_t) 1 << power;
  sieve_t *sieve = create_sieve(upper_bound);
  if (NULL == sieve) {
    fprintf(stderr, "Failed to create SMALL_PRIMES sieve of length %"PRId64".\n"\
            "This failure can occur if there is insufficient physical memory on the system.\n"\
            "Aborting.\n", upper_bound);
    exit(1);
  }

  // initilize it this way would turn all bits that corresponds
  // to even number off. This would save time because we don't
  // have to mark them as composite later (Here odd bits corresponds
  // to even integers since the count starts from zeroth bit)
  init_sieve_with_odd_bits_off(sieve, upper_bound);

  mark_composite(sieve, 0);
  mark_composite(sieve, 1);
  mark_prime(sieve, 2);

  // Scan the entries of the sieve from 3 to UPPER_BOUND.
  // The case of prime 2 is already taken care of in init_sieve_with_odd_bits_off.
  // All the primes after 2 are odd, so loop over odd integers only
  for (int64_t i = 3; i < upper_bound; i+=2) {
    tbassert(trialdiv_prime_p(i) == prime_p(sieve, i),
             "Incorrect primality recorded for %"PRId64" (%d vs %d)\n",
             i, trialdiv_prime_p(i), prime_p(sieve, i));

    // Skip any I marked as composite
    if (!prime_p(sieve, i)) {
      continue;
    }

    // At this point, I is prime.
    // Mark all multiples of I as composite.
    for (int64_t temp = 2*i; temp < upper_bound; temp += i) {
      mark_composite(sieve, temp);
    }
  }
  return sieve;
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
//   SMALL_PRIMES -- Sieve recording all primes.
//
static int64_t count_primes_in_interval_helper(int64_t start, int64_t length,
                                               const sieve_t* small_primes) {
  // Initially all numbers are considered as primes. Once we mark an
  // integer as composite, we decrement num_primes by 1
  uint64_t num_primes = length;

  // Using these init methods, we would mark each even integer as composite
  // if start is an even integer
  if (start % 2 == 0) {
    // ex: 10101010
    init_sieve_with_odd_bits_off(large_primes, length);
    // Subtract the number of even integers that are marked as composite
    num_primes -= (length + 1)/2;
  // if start is an odd integer
  } else {
    // ex: 01010101
    init_sieve_with_even_bits_off(large_primes, length);
    // Subtract the number of even integers that are marked as composite
    num_primes -= length/2;
  }

  // if [START, START+LENGTH) includes 2 then mark 2 as prime
  if (start <= 2) {
    mark_prime(large_primes, 2 - start);
    ++num_primes;
  }

  // Scan all of the potentially prime entries in the SMALL_PRIMES
  // sieve. The case of 2 is already taken care of inside
  // init_sieve methods (both for even start and odd start) above.
  // All primes after 2 are all odd, so loop over odd integers only.
  for (int64_t p = 3; p < small_primes->length; p+=2) {
    tbassert(trialdiv_prime_p(p) == prime_p(small_primes, p),
             "Incorrect primality recorded for %"PRId64" in small_primes\n",
             p);

    // Skip any entry in SMALL_PRIMES marked as composite.
    if (!prime_p(small_primes, p)) {
      continue;
    }

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

    /* DEBUG_EPRINTF("kp_index = %"PRId64"\n", kp_index); */

    // Mark all multiples of P in [KP_INDEX, KP_INDEX+LENGTH) as
    // composite.
    for ( ; kp_index < length; kp_index += p) {
      if (!prime_p(large_primes, kp_index)) {
        continue;
      }
      mark_composite(large_primes, kp_index);
      --num_primes;
    }
  }

  return num_primes;
}

/*************************************************************************
 * Definitions for methods in header file.                               
 *************************************************************************/

int64_t count_primes_in_interval(int64_t start, int64_t length) {
  int64_t num_primes;
  uint64_t max = start + length;

  // Return 0 primes for nonpositive-length intervals.
  if (length <= 0) {
    return 0;
  }

  // Return 0 primes for intervals whose high endpoint is at most 2.
  // Because we treat all negative numbers as composite, there are no
  // primes less than 2.
  if (max <= 2) {
    return 0;
  }

  // Ensure that the smallest value of START is 2.
  if (start < 2) {
    length -= 2 - start;
    start = 2;
  }

  // round max to a power of 2
  --max;
  max |= max >> 1;
  max |= max >> 2;
  max |= max >> 4;
  max |= max >> 8;
  max |= max >> 16;
  max |= max >> 32;
  ++max;

  // locate the set bit in max (start from 0)
  int set_bit = 0;
  while (!(max & ((uint64_t) 1 << set_bit)))
    set_bit++;

  // compute the power of the small primes sieve to be created
  int power = (set_bit / 2) + !(set_bit % 2 == 0);
  // Create SMALL_PRIMES structure to record the primes less than 2^power
  sieve_t *small_primes = find_small_primes(power);

  // initialize large_primes to be used inside count_primes_in_interval_helper
  large_primes = create_sieve(MAX_SIEVE_LENGTH);
  if (NULL == large_primes) {
    fprintf(stderr, "Failed to create LARGE_PRIMES sieve of length %"PRId64".\n"\
            "This can happen if there is insufficient physical memory on the system.\n"\
            "Aborting.\n", length);
    exit(1);
  }

  // Initialize NUM_PRIMES
  num_primes = 0;
  // Segment the interval [START, START+LENGTH) into subintervals no
  // longer than MAX_SIEVE_LENGTH.
  while (length > MAX_SIEVE_LENGTH) {
    // Count the number of primes in this segment, and add this count
    // to NUM_PRIMES.
    num_primes += count_primes_in_interval_helper(start, MAX_SIEVE_LENGTH,
                                                  small_primes);
    // Update START and LENGTH to handle the next segment
    start += MAX_SIEVE_LENGTH;
    length -= MAX_SIEVE_LENGTH;
  }
  // Count the number of primes in the final segment, and add the
  // count to NUM_PRIMES.
  num_primes += count_primes_in_interval_helper(start, length, small_primes);

  // Free SMALL_PRIMES.
  destroy_sieve(small_primes);

  // Free LARGE_PRIMES structure
  destroy_sieve(large_primes);

  return num_primes;
}
