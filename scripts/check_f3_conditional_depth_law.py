#!/usr/bin/env python3
"""Finite conditional atom regression; not Lean/Haar verification."""
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

def v(x):
    if x == 0:
        return None
    n = 0
    while x % 3 == 0:
        x //= 3
        n += 1
    return n

rows = []
for L in range(1, 5):
    for extra in range(2, 5):
        N = L + extra
        a, b = 1, 1 + 3 ** L
        success, counts, root_hits = 0, Counter(), 0
        for d in range(3 ** N):
            if d % 3 == 0:
                continue
            r, s = v(d-a), v(d-b)
            if r != s:
                success += 1
                if r is None or s is None:
                    root_hits += 1
                else:
                    counts[r-s] += 1
        assert success == 2 * 3 ** (N-L-1)
        assert root_hits == 2 and counts[0] == 0
        for h in range(1, N-L):
            assert Fraction(counts[h], success) == Fraction(1, 3**h)
            assert Fraction(counts[-h], success) == Fraction(1, 3**h)
            assert Fraction(counts[h]+counts[-h], success) == Fraction(2, 3**h)
        assert sum(counts.values()) + root_hits == success
        rows.append({'L':L, 'precision':N, 'conditioning_event_count':success,
                     'root_hit_representatives_kept_in_condition':root_hits,
                     'finite_signed_counts':dict(sorted(counts.items()))})
out={'status':'finite conditional regression only, not kernel proof',
     'boundary':'L+abs(h)<N; genuine root representatives remain undefined in finite signed atoms',
     'cases':len(rows),'rows':rows}
Path('reports/f3_conditional_depth_law_sanity.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'PASS: {len(rows)} actual conditional finite-residue cases')
