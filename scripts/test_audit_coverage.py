#!/usr/bin/env python3
"""Negative tests: the imported RUN producer never weakens project coverage."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_audit_coverage as audit


class AuditCoverageTests(unittest.TestCase):
    def check(self, names):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'OmegaBalance').mkdir()
            (root / 'scripts').mkdir()
            (root / 'OmegaBalance/T.lean').write_text(
                'namespace OmegaBalance\ntheorem foo : True := True.intro\nend OmegaBalance\n')
            (root / 'scripts/Audit.lean').write_text(
                ''.join(f'#print axioms {name}\n' for name in names))
            with patch.object(audit, 'ROOT', root), contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                return audit.main()

    def test_exact_coverage(self):
        self.assertEqual(self.check(['OmegaBalance.foo', 'MaynardBFT.consecutive_primes']), 0)

    def test_missing_project(self):
        self.assertEqual(self.check(['MaynardBFT.consecutive_primes']), 1)

    def test_missing_producer(self):
        self.assertEqual(self.check(['OmegaBalance.foo']), 1)

    def test_unknown_entry(self):
        self.assertEqual(self.check(['OmegaBalance.foo', 'MaynardBFT.consecutive_primes',
                                     'MaynardBFT.unregistered']), 1)

    def test_duplicate_project(self):
        self.assertEqual(self.check(['OmegaBalance.foo', 'OmegaBalance.foo',
                                     'MaynardBFT.consecutive_primes']), 1)

    def test_duplicate_producer(self):
        self.assertEqual(self.check(['OmegaBalance.foo', 'MaynardBFT.consecutive_primes',
                                     'MaynardBFT.consecutive_primes']), 1)


if __name__ == '__main__':
    unittest.main()
