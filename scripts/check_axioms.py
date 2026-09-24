#!/usr/bin/env python3
"""Check actual #print axioms output; source scanning is not a kernel audit."""
from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: python3 scripts/check_axioms.py axioms.log", file=sys.stderr)
        return 2
    text = Path(sys.argv[1]).read_text(encoding="utf-8")
    commands = re.findall(r"^#print axioms (\S+)$", (ROOT / "scripts/Audit.lean").read_text(), re.M)
    reported = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
    found = {name for name, _ in reported} | set(empty)
    errors = [f"Missing audit result: {name}" for name in commands if name not in found]
    for name, axioms in reported:
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        unexpected = used - ALLOWED
        if unexpected:
            errors.append(f"{name}: unexpected axioms: {sorted(unexpected)}")
    if not commands:
        errors.append("Audit.lean contains no audit commands")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Axiom audit PASS: {len(commands)} declarations; only standard Lean axioms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
