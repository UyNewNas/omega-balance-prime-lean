#!/usr/bin/env python3
"""Explore F3(n)=v3(n+1)-v3(n-1), with exact finite verification.

Only the Python standard library is required. Computations do not prove the
prime-distribution or consecutive-prime theorems; those require external
number-theoretic results.

Usage: python f3_corollaries_verify.py --limit 10000000
"""
from __future__ import annotations

import argparse
from collections import Counter
from math import isqrt
from random import Random
from time import perf_counter


def v3(n: int) -> int:
    if n == 0:
        raise ValueError('v3(0) is infinite, not a finite integer.')
    n = abs(n)
    k = 0
    while n % 3 == 0:
        n //= 3
        k += 1
    return k


def f3(n: int) -> int:
    if n < 2:
        raise ValueError('This implementation requires n >= 2.')
    return v3(n + 1) - v3(n - 1)


def sign(n: int) -> int:
    return (n > 0) - (n < 0)


def sieve(limit: int) -> bytearray:
    if limit < 5:
        raise ValueError('limit must be >= 5')
    flags = bytearray(b'\x01') * (limit + 1)
    flags[0:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            start = p * p
            flags[start:limit+1:p] = b'\x00' * ((limit - start) // p + 1)
    return flags


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O: finite verification uses assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=10_000_000)
    args = parser.parse_args()
    start_time = perf_counter()
    flags = sieve(args.limit)
    primes = [p for p in range(5, args.limit + 1, 2) if flags[p]]
    values = [f3(p) for p in primes]
    counts = Counter(values)
    print(f'Range: 3 < p <= {args.limit}; number of primes: {len(primes)}')
    print('k\tF3=+k count\tF3=-k count\t|F3|=k percent\tlimiting percent')
    for k in range(1, max(map(abs, values)) + 1):
        n = counts[k] + counts[-k]
        print(f'{k}\t{counts[k]}\t{counts[-k]}\t{100*n/len(primes):.8f}\t{200/(3**k):.8f}')
    print('Signed empirical mean:', sum(values)/len(values))
    print('Empirical mean absolute value:', sum(map(abs, values))/len(values))
    print('Empirical second moment:', sum(x*x for x in values)/len(values))

    longest: dict[int, tuple[int, int]] = {}
    first: dict[tuple[int, int], list[int]] = {}
    run_start = 0
    for i, value in enumerate(values):
        if i == 0 or value != values[i-1]:
            run_start = i
        length = i-run_start+1
        if length > longest.get(value, (0, 0))[0]:
            longest[value] = (length, run_start)
        if length in (2, 3, 4, 5, 6) and (value, length) not in first:
            first[(value, length)] = primes[run_start:i+1]
    print('\nFirst examples of exact constant runs of consecutive primes:')
    for value in (1, -1, 2, -2, 3, -3):
        for length in (3, 4, 5):
            if (value, length) in first:
                print(value, length, first[(value, length)])
    print('Longest runs by value:')
    for value in (1, -1, 2, -2, 3, -3):
        if value in longest:
            length, i = longest[value]
            print(value, length, primes[i:i+length])

    checks = Counter()
    # Universal local formulas on arbitrary integers, not just primes.
    integers = [n for n in range(2, 301) if n % 3]
    for n in integers:
        A = f3(n)
        for exponent in range(1, 16):
            expected_abs = abs(A)+v3(exponent)
            expected_sign = sign(A) if exponent % 2 else -1
            assert f3(n**exponent) == expected_sign*expected_abs
            checks['power_identity'] += 1
        for m in integers:
            B = f3(m)
            C = f3(n*m)
            assert sign(C) == -sign(A)*sign(B)
            if abs(A) != abs(B):
                assert abs(C) == min(abs(A), abs(B))
            else:
                assert abs(C) >= abs(A)
            checks['multiplication_identity'] += 1
    # General exact gap formula when the two depths differ.
    small = [p for p in primes if p <= 2000]
    for i, p in enumerate(small):
        for q in small[i+1:]:
            A, B = f3(p), f3(q)
            adjusted_gap = q-p+sign(B)-sign(A)
            if abs(A) != abs(B):
                assert adjusted_gap != 0
                assert v3(adjusted_gap) == min(abs(A), abs(B))
                checks['unequal_depth_gap'] += 1
            elif adjusted_gap:
                assert v3(adjusted_gap) >= abs(A)
                checks['equal_depth_gap'] += 1
    # Reflection locking, tested on all coprime-to-3 integer splits.
    for N in range(6, 2001, 6):
        s = v3(N)
        for a in range(2, N-1):
            b = N-a
            if a % 3 and 0 < abs(f3(a)) < s:
                assert f3(b) == -f3(a)
                checks['reflection_locking'] += 1
    # Independent trial-division primality checks on 500 random sieve positions.
    rng = Random(30924)
    for _ in range(500):
        n = rng.randint(2, args.limit)
        trial = all(n % d for d in range(2, isqrt(n)+1))
        assert bool(flags[n]) == trial
        checks['independent_primality'] += 1
    print('\nFinite identity checks:', dict(checks))
    print('Total checks:', sum(checks.values()), 'PASS')
    print(f'Elapsed seconds: {perf_counter()-start_time:.3f}')

if __name__ == '__main__':
    main()
