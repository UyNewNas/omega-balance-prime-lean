#!/usr/bin/env python3
"""Require one axiom-registry entry for every project theorem declaration.

The project namespace is OmegaBalance (AGENTS.md). This registry check is
not a substitute for compiling the declarations or evaluating their axioms.
"""
from collections import Counter
from pathlib import Path
import re
import sys
from check_sources import erase_comments_and_strings

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(r"\btheorem\s+([\w'.]+)", re.UNICODE)
AUDIT = re.compile(r"#print\s+axioms\s+([\w'.]+)", re.UNICODE)


def main() -> int:
    expected: dict[str, list[str]] = {}
    sources = [ROOT / "OmegaBalance.lean", *sorted((ROOT / "OmegaBalance").rglob("*.lean"))]
    for path in sources:
        clean = erase_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in DECL.finditer(clean):
            name = match.group(1)
            if not name.startswith("OmegaBalance."):
                name = "OmegaBalance." + name
            expected.setdefault(name, []).append(str(path.relative_to(ROOT)))
    text = erase_comments_and_strings((ROOT / "scripts/Audit.lean").read_text(encoding="utf-8"))
    actual = Counter(AUDIT.findall(text))
    failures = []
    for label, names in [
        ("Missing audits", sorted(set(expected) - set(actual))),
        ("Unknown audit targets", sorted(set(actual) - set(expected))),
        ("Repeated audit targets", sorted(n for n, count in actual.items() if count != 1)),
        ("Duplicate declaration names", sorted(n for n, paths in expected.items() if len(paths) != 1)),
    ]:
        if names:
            failures.append(label + ": " + ", ".join(names))
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"Audit coverage PASS: {len(expected)} theorem declarations, each listed once.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
