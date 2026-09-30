#!/usr/bin/env python3
"""Finite regression evidence, NOT a proof of a prime asymptotic."""
from collections import Counter
from fractions import Fraction
import json
MODULUS = 3 ** 5

def v3(n):
    if n == 0:
        return None
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e

counts = Counter()
witnesses = {}
for n in range(MODULUS):
    for r in range(MODULUS):
        if (n % 3, r % 3) not in ((1, 1), (2, 2)):
            continue
        d = 5 * r
        depths = tuple(v3((n + 6 * j * d) * (n + (6 * j + 2) * d) + 1) for j in range(3))
        counts['allowed'] += 1
        if depths == (3, 4, 2):
            counts['event'] += 1
            counts['d_mod3_' + str(d % 3)] += 1
            witnesses.setdefault(d % 3, [n, r, d])
result = dict(modulus=MODULUS, counts=dict(counts), witnesses=witnesses, ratio=str(Fraction(counts['event'], counts['allowed'])))
assert counts == {'allowed': 13122, 'event': 72, 'd_mod3_1': 36, 'd_mod3_2': 36}
assert result['ratio'] == '4/729'
print(json.dumps(result, indent=2))
