#!/usr/bin/env python3
"""Boundary regressions; finite tests, not Lean kernel proofs."""
import unittest
from f3_corollaries_verify import f3, sign, v3


def total_v3(n: int) -> int:
    """Match mathlib's totalized value at zero, only in this adapter."""
    return 0 if n == 0 else v3(n)


def f3_int(n: int) -> int:
    return total_v3(n + 1) - total_v3(n - 1)


class F3BoundaryTests(unittest.TestCase):
    def test_ordinary_valuation_rejects_zero(self):
        with self.assertRaises(ValueError):
            v3(0)

    def test_positive_interface_domain(self):
        for n in (-2, -1, 0, 1):
            with self.assertRaises(ValueError):
                f3(n)

    def test_integer_oddness(self):
        for n in range(-1000, 1001):
            self.assertEqual(f3_int(-n), -f3_int(n))

    def test_positive_compatibility(self):
        for n in range(2, 1001):
            self.assertEqual(f3_int(n), f3(n))

    def test_zero_classification(self):
        for n in range(2, 1001):
            self.assertEqual(f3(n) == 0, n % 3 == 0)
        self.assertEqual(f3_int(1), 0)  # zero classification needs n>1
        self.assertNotEqual(1 % 3, 0)

    def test_composites_retain_arithmetic_laws(self):
        for n, expected in ((25, -1), (125, 2), (343, -2), (323, 4), (325, -4)):
            self.assertEqual(f3(n), expected)

    def test_equal_depth_can_increase_on_multiplication(self):
        self.assertEqual((abs(f3(2)), abs(f3(4))), (1, 1))
        self.assertEqual(abs(f3(2 * 4)), 2)

    def test_adjusted_gaps_without_ordering(self):
        for p in range(2, 100):
            for q in range(2, 100):
                if p % 3 and q % 3 and abs(f3(p)) != abs(f3(q)):
                    h = q - p + sign(f3(q)) - sign(f3(p))
                    self.assertNotEqual(h, 0)
                    self.assertEqual(v3(h), min(abs(f3(p)), abs(f3(q))))

    def test_reflection_including_odd_totals(self):
        for N in range(6, 301, 3):
            for a in range(2, N - 1):
                if a % 3 and abs(f3(a)) < v3(N):
                    self.assertEqual(f3(N - a), -f3(a))
        self.assertEqual(f3(7), -f3(2))  # odd total 9

    def test_reflection_threshold_is_strict(self):
        self.assertEqual(abs(f3(11)), v3(30))
        self.assertNotEqual(f3(19), -f3(11))

    def test_opposites_do_not_imply_twins(self):
        self.assertEqual(f3(13), -f3(5))
        self.assertNotEqual(13 - 5, 2)


if __name__ == '__main__':
    unittest.main(verbosity=2)
