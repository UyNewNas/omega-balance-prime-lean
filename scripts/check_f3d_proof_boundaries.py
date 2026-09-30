#!/usr/bin/env python3
"""Finite exact-arithmetic regression certificates; not Lean or asymptotic proofs.

Run from any directory. JSON is written to stdout so committed evidence is
reproducible with no mutation of mathematical source or audit configuration.
The all-M argument and the scope of the correction are in the accompanying
report. Passing these finite checks does not certify generalized F3D theory.
"""
from itertools import product
import json


def v3(n: int) -> int:
    """Valuation only on nonzero signed integers; never totalize zero here."""
    if n == 0:
        raise ValueError("this certificate requires a nonzero argument")
    n = abs(n)
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def f(n: int, d: int) -> int:
    assert n != d and n != -d
    return v3(n + d) - v3(n - d)


def grid(t: tuple[int, ...]) -> list[tuple[int, int]]:
    assert all(x >= 0 for x in t)
    xs = [(3**x + 1, 3**x - 1) for x in t]
    assert tuple(f(n, d) for n, d in xs) == t
    return xs


def witness(xs: list[tuple[int, int]]) -> tuple[int, int]:
    u = [n + d for n, d in xs]
    assert len(u) == 3 and all(z != 0 for z in u)
    p = (u[0] - u[1])**2 + 3*u[2]**2
    q = 0
    assert p > 0 and f(p, q) == 0
    return p, q


def main() -> None:
    pairs = []
    for m in range(65):
        left, right = (0, 0, m), (1, 0, m)
        p, _ = witness(grid(left))
        p_prime, _ = witness(grid(right))
        values = [v3(p), v3(p_prime)]
        distance = max(abs(a-b) for a, b in zip(left, right))
        assert values == [2*m+1, 0] and distance == 1
        assert (4 + 3**(2*m+1)) % 3 == 1
        pairs.append({"M": m, "valuations": values, "sup_distance": distance})

    # Exercise every finite unit-grid point for D=2 at a bounded depth range.
    unit_checks = 0
    for t in product(range(3), repeat=3):
        for units in product((1, 4, 7), repeat=6):
            xs = []
            for i, exponent in enumerate(t):
                u = 2*3**exponent*units[2*i]
                v = 2*units[2*i+1]
                xs.append(((u+v)//2, (u-v)//2))
            assert tuple(f(n, d) for n, d in xs) == t
            witness(xs)
            unit_checks += 1
    assert unit_checks == 19683

    # m=1: the output polynomials are exactly P=n_1, Q=d_1.
    # Their syntactic monomial exponents certify the displayed degree upper
    # bound without treating the sample evaluations as a lower-bound proof.
    monomials = {"P": [[1, 0]], "Q": [[0, 1]]}
    degree = max(sum(exponents) for poly in monomials.values() for exponents in poly)
    assert degree == 1 and degree < 3*1
    identity_checks = 0
    for n, d in product(range(-20, 21), repeat=2):
        if n == d or n == -d:
            continue
        p, q = n, d
        assert f(p, q) == f(n, d)
        identity_checks += 1
    assert identity_checks == 1600
    assert f(2, 0) == 0 and f(4, 2) == 1

    result = {
        "review_id": "F3D-PROOF-BOUNDARY-CORRECTIONS-2026-09-30",
        "source_base_commit": "e59f4e4dc729a12e693594ff4dd996f1bb57f6b9",
        "evidence_kind": "FINITE_EXACT_ARITHMETIC_REGRESSION_ONLY",
        "lean_kernel_verified": False,
        "general_classification_or_degree_theory_certified": False,
        "asymptotic_or_all_parameter_claim_verified_by_script": False,
        "multi_l12": {
            "polynomial_pair": ["(u1-u2)^2 + 3*u3^2", "0"],
            "D": 2,
            "S_D": [1, 4, 7],
            "fixed_units": [1, 1, 1, 1, 1, 1],
            "adjacent_pairs_checked": len(pairs),
            "adjacent_pair_checks": pairs,
            "all_unit_grid_checks_at_depths_0_through_2": unit_checks,
            "output_f_is_zero_in_all_checked_instances": True,
            "claim_refuted_by_written_all_M_argument": "fixed-grid tropical equivalence",
            "not_refuted": ["discontinuous finite affine partition property", "main classification", "constructive sufficiency"],
        },
        "tern6": {
            "required_hypothesis": "m >= 2",
            "excluded_boundary": "m = 1",
            "identity_pair": ["n1", "d1"],
            "identity_monomial_exponents": monomials,
            "identity_pair_degree": degree,
            "implied_minimum_degree_upper_bound": 1,
            "unguarded_lower_bound_at_m1": 3,
            "signed_legal_input_checks": identity_checks,
        },
        "all_finite_checks_passed": True,
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
