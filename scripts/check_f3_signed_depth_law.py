#!/usr/bin/env python3
"""Finite residue regression only; no claim of Haar/kernel verification."""
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

def valuation(x):
    if x == 0:
        return None
    t = 0
    while x % 3 == 0:
        t += 1
        x //= 3
    return t

rows = []
for L in range(1, 5):
    for extra in range(2, 5):
        N = L + extra
        modulus = 3 ** N
        a, b = 1, 1 + 3 ** L
        counts, undefined = Counter(), 0
        units = [d for d in range(modulus) if d % 3]
        for d in units:
            r, s = valuation(d - a), valuation(d - b)
            if r is None or s is None:
                undefined += 1
            else:
                counts[r - s] += 1
        assert undefined == 2
        assert Fraction(counts[0], len(units)) == 1 - Fraction(1, 3 ** L)
        for h in range(1, N - L):
            expected = Fraction(1, 3 ** (L + h))
            assert Fraction(counts[h], len(units)) == expected
            assert Fraction(counts[-h], len(units)) == expected
        assert sum(counts.values()) + undefined == len(units)
        rows.append({'L': L, 'precision': N, 'unit_representatives': len(units),
                     'root_hit_representatives_excluded': undefined,
                     'signed_atom_counts': dict(sorted(counts.items()))})
out = {'status': 'finite regression only, not kernel proof or null-singleton proof',
       'precision_boundary': 'atoms checked only for L+abs(h)<N; root residue representatives remain undefined',
       'cases': len(rows), 'sample_representatives': sum(r['unit_representatives'] for r in rows),
       'rows': rows}
Path('reports/f3_signed_depth_law_sanity.json').write_text(json.dumps(out, indent=2)+'\n')
print(f"PASS: {len(rows)} cases, {out['sample_representatives']} representatives; root hits never zero-totalized")
