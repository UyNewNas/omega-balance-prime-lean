#!/usr/bin/env python3
"""Fail when a project theorem lacks a #print axioms entry.

This repository uses the OmegaBalance namespace and explicit theorem names.
Comments and strings are erased by the same parser as the proof-escape guard.
This checks coverage only; check_axioms.py checks actual kernel audit output.
"""
from collections import Counter
from pathlib import Path
import re
import sys
from check_sources import erase_comments_and_strings

ROOT = Path(__file__).resolve().parents[1]
# Explicit imported producer audit, in addition to every project declaration.
# This is a required entry, not a wildcard exemption from coverage or axiom checks.
REQUIRED_EXTERNAL = {'MaynardBFT.consecutive_primes'}


def main() -> int:
    expected = set()
    for path in sorted((ROOT / 'OmegaBalance').rglob('*.lean')):
        text = erase_comments_and_strings(path.read_text(encoding='utf-8'))
        for name in re.findall(r'\b(?:theorem|lemma)\s+([^\s:({]+)', text):
            expected.add('OmegaBalance.' + name)
    audit = erase_comments_and_strings((ROOT / 'scripts/Audit.lean').read_text(encoding='utf-8'))
    names = re.findall(r'^#print axioms (\S+)\s*$', audit, re.M)
    found = set(names)
    required = expected | REQUIRED_EXTERNAL
    errors = [f'Missing audit entry: {name}' for name in sorted(required - found)]
    errors += [f'Audit entry without registered declaration: {name}' for name in sorted(found - required)]
    errors += [f'Duplicate audit entry: {name}' for name, count in Counter(names).items() if count != 1]
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'Audit coverage PASS: all {len(expected)} project declarations and '
          f'{len(REQUIRED_EXTERNAL)} required external producer covered exactly once.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
