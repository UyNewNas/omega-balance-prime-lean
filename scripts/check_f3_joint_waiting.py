#!/usr/bin/env python3
"""Finite residue sanity checks for REC-L7; not a Lean/kernel proof.

The first K+1 ternary digits decide pairwise unequal-depth events. Exact
integer root hits retain infinite depth. A missing finite-prefix hit is
censored as infinity only for the comparison with that prefix length.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, exp, inf
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def depth(d, a):
    n = abs(d - a)
    if n == 0:
        return inf
    k = 0
    while n % 3 == 0:
        n //= 3
        k += 1
    return k


def main():
    configs = [(1, 4), (1, 4, 7), (1, 4, 10), (2, 5, 11), (1, 10), (1, 28),
               (1, 4, 10, 13)]
    results = []
    total = 0
    root_hits = 0
    for roots in configs:
        m = len(roots)
        pairs = list(combinations(range(m), 2))
        assert len(pairs) == comb(m, 2)
        distances = {(i, j): depth(roots[i], roots[j]) for i, j in pairs}
        K = max(distances.values())
        units = [d for d in range(3 ** (K + 1)) if d % 3]
        depths = {d: [depth(d, a) for a in roots] for d in units}
        target = [[depth(a, b) for b in roots] for a in roots]
        for T in range(4):
            joint_fail = 0
            pair_fail = Counter()
            batches = 0
            for samples in product(units, repeat=T):
                batches += 1
                total += 1
                root_hits += any(d in roots for d in samples)
                first = {}
                matrix = [[inf if i == j else None for j in range(m)] for i in range(m)]
                for i, j in pairs:
                    first[i, j] = inf
                    for t, d in enumerate(samples, 1):
                        if depths[d][i] != depths[d][j]:
                            first[i, j] = t
                            matrix[i][j] = matrix[j][i] = min(depths[d][i], depths[d][j])
                            break
                    if first[i, j] == inf:
                        pair_fail[i, j] += 1
                    else:
                        assert matrix[i][j] == distances[i, j]
                stopped = max(first.values()) <= T
                recovered = matrix == target
                assert stopped == recovered
                missing = any(all(depths[d][i] == depths[d][j] for d in samples)
                              for i, j in pairs)
                assert missing == (not stopped)
                joint_fail += missing
            joint_probability = Fraction(joint_fail, batches)
            exact_union_bound = 0
            for p, L in distances.items():
                law = (1 - Fraction(1, 3 ** L)) ** T
                assert Fraction(pair_fail[p], batches) == law
                exact_union_bound += law
            assert joint_probability <= min(Fraction(1), exact_union_bound)
            envelope = min(1., comb(m, 2) * exp(-T / (3 ** K)))
            assert float(joint_probability) <= envelope + 1e-14
            if T == 0:
                assert joint_probability == 1
            results.append({'roots': roots, 'm': m, 'B': comb(m, 2), 'K': K,
                            'T': T, 'batches': batches,
                            'joint_failure_probability': str(joint_probability),
                            'exponential_envelope': envelope})
    report = {'status': 'finite sanity PASS; not a kernel proof',
              'base_commit': '338442744c906dae107b65e83f010f0b76d71ad2',
              'cases': len(results), 'batches_checked': total,
              'batches_containing_exact_root_hit': root_hits,
              'checks': ['canonical choose-two count', 'actual finite maximum K',
                         'root-hit infinity', 'full symmetric matrix and infinite diagonal',
                         'first-hit maximum iff scan recovery', 'tail union equivalence',
                         'exact per-pair finite-residue law', 'union/exponential bounds',
                         'T=0 failure with m>=2'],
              'results': results}
    path = ROOT / 'reports/f3_joint_waiting_semantic_sanity.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Joint waiting finite sanity PASS: {total} batches in {len(results)} cases; '
          f'{root_hits} batches include exact root hits. Not a kernel check.')


if __name__ == '__main__':
    main()
