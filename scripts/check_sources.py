#!/usr/bin/env python3
"""Reject proof escapes in project Lean sources (not dependency sources)."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|ofReduceNat|implemented_by)\b")


def erase_comments_and_strings(text: str) -> str:
    """Preserve newlines for diagnostics; understand nested Lean block comments."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            if text[i] == "\\":
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                quoted = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated comment or string")
    return "".join(out)


def main() -> int:
    sources = [ROOT / "OmegaBalance.lean", *sorted((ROOT / "OmegaBalance").rglob("*.lean")),
               *sorted((ROOT / "scripts").glob("*.lean"))]
    failures = []
    for path in sources:
        clean = erase_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in FORBIDDEN.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(ROOT)}:{line}: forbidden {match.group()}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"Source audit PASS: {len(sources)} Lean files, no proof escapes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
