#!/usr/bin/env python3
"""Finite sanity checks for F3-PAT-1; not an infinitude proof or Lean audit.

Run from any directory. Only the Python standard library is required.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path

Q = 729
H = (0, 38, 92, 146)
BASE = "f7033c1625b2fc36d76544488ba0402a0a1619fc"


def v3(n: int) -> int:
    if n <= 0:
        raise ValueError("The paper valuation is defined only on positive integers")
    exponent = 0
    while n % 3 == 0:
        n //= 3
        exponent += 1
    return exponent


def f3(n: int) -> int:
    if n <= 1:
        raise ValueError("F3 requires n > 1")
    return v3(n + 1) - v3(n - 1)


def prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % divisor for divisor in range(3, isqrt(n) + 1, 2))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def values(n: int, d: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    numbers = tuple(n + h * d for h in H)
    return tuple(map(f3, numbers)), tuple(f3(n * x) for x in numbers[1:])


def forms(u: int, v: int) -> tuple[int, ...]:
    return tuple(5 + h + Q * u + Q * h * v for h in H)


def main() -> None:
    expected = ((1, -1, -1, -1), (3, 5, 3))
    residue_lifts = 0
    for r in range(1, 8):
        modulus = 3 ** r
        for b in range(1, modulus):
            for j in range(5):
                require(v3(b + j * modulus) == v3(b), "valuation lift")
                residue_lifts += 1

    pattern_checks = 0
    for u in range(100):
        for v in range(100):
            n, d = 5 + Q * u, 1 + Q * v
            require(forms(u, v) == tuple(n + h * d for h in H), "forms")
            require(values(n, d) == expected, "seven exact F3 values")
            pattern_checks += 1

    determinants = [Q * Q * (H[j] - H[i])
                    for i in range(4) for j in range(i + 1, 4)]
    require(all(det != 0 for det in determinants), "nonparallel directions")
    local_rows = []
    residue_pairs = 0
    for ell in filter(prime, range(2, 200)):
        count = sum(all(x % ell for x in forms(u, v))
                    for u in range(ell) for v in range(ell))
        residue_pairs += ell ** 2
        nu = len({h % ell for h in H})
        predicted = ell ** 2 if ell == 3 else (ell - 1) * (ell + 1 - nu)
        require(count == predicted and count > 0, f"local count at {ell}")
        if ell != 3:
            inv = pow(Q, -1, ell)
            u, v = (-4 * inv) % ell, (-inv) % ell
            require(all(x % ell == 1 for x in forms(u, v)), "local witness")
        beta = Fraction(count, ell ** 2) * Fraction(ell, ell - 1) ** 4
        if ell > 146:
            require(beta == Fraction(ell ** 2 * (ell - 3), (ell - 1) ** 3),
                    "large-prime factor")
        local_rows.append({"prime": ell, "admissible_pairs": count,
                           "beta": str(beta)})

    witnesses = []
    for n, d in ((5, 1), (149, 55)):
        nums = tuple(n + h * d for h in H)
        require(all(map(prime, nums)), "witness primality")
        require(values(n, d) == expected, "witness F3 values")
        witnesses.append({"n": n, "d": d, "primes": nums,
                          "in_sufficient_class": (n % Q, d % Q) == (5, 1)})

    report = {
        "result_id": "F3-PAT-1",
        "result_status_source": "docs/proofs/f3/four_prime_construction/theorem.md",
        "repository_base": BASE,
        "check_status": "PASS",
        "scope": "Finite arithmetic sanity checks only; not Lean or infinitude verification",
        "valuation_lift_checks": residue_lifts,
        "parameter_pattern_checks": pattern_checks,
        "nonparallel_determinants": determinants,
        "local_primes_checked": len(local_rows),
        "local_residue_pairs_enumerated": residue_pairs,
        "checked_primes": [row["prime"] for row in local_rows],
        "witnesses": witnesses,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "paper_audit": "not_assessed_by_this_script",
        "lean_verification": "not_run_by_this_script",
    }
    target = Path(__file__).resolve().parents[1] / "reports/f3_pat1_paper_check.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "result_id", "check_status", "valuation_lift_checks", "parameter_pattern_checks",
        "local_primes_checked", "local_residue_pairs_enumerated")}, ensure_ascii=False))
    print(target)


if __name__ == "__main__":
    main()
