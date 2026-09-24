#!/usr/bin/env python3
"""Run the repository's checks on Linux, macOS, or Windows; fail on any error."""
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(command: list[str], log_name: str | None = None) -> None:
    print("+ " + " ".join(command), flush=True)
    if log_name is None:
        subprocess.run(command, cwd=ROOT, check=True)
        return
    with (ROOT / log_name).open("w", encoding="utf-8") as log:
        with subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True,
                              encoding="utf-8", errors="replace") as proc:
            assert proc.stdout is not None
            for line in proc.stdout:
                print(line, end="", flush=True)
                log.write(line)
            status = proc.wait()
    if status:
        raise subprocess.CalledProcessError(status, command)


def main() -> int:
    if shutil.which("lake") is None:
        print("lake was not found. Install elan and fetch the pinned dependencies first.",
              file=sys.stderr)
        return 2
    try:
        run([sys.executable, "scripts/check_sources.py"])
        run([sys.executable, "scripts/check_audit_coverage.py"])
        run(["lake", "build"], "build.log")
        run(["lake", "build", "OmegaBalance.Examples", "OmegaBalance.F3Examples",
             "OmegaBalance.FactorSumExamples"], "examples.log")
        run(["lake", "env", "lean", "scripts/Audit.lean"], "axioms.log")
        run([sys.executable, "scripts/check_axioms.py", "axioms.log"])
        run([sys.executable, "scripts/f3_corollaries_verify.py", "--limit", "10000000"], "f3.log")
        run([sys.executable, "scripts/test_f3_corollaries.py"], "f3-boundaries.log")
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"Verification FAILED: {exc}", file=sys.stderr)
        return 1
    print("Verification PASS: library, regression proofs, source guard, complete axiom audit, and finite F3 checks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
