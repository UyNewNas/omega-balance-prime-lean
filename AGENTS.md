# Repository conventions

- Work in namespace `OmegaBalance`; preserve explicit public theorem hypotheses.
- Ω counts WITH multiplicity. Never silently replace it by distinct-factor ω.
- Use `ℤ` for every signed statistic, casting each term BEFORE subtraction.
- `omegaDiff` and `f3` are different statistics; do not transfer the twin symmetry between them.
- Preserve mathlib's totalized zero conventions. Require positive/nonzero arguments where needed.
- Do not add proof placeholders, custom axioms, unsafe declarations, or native proof escapes.
- Reuse mathlib factorization and prime APIs rather than re-proving their foundations.
- Keep infinitude and gap claims separate from finite/residue-class lemmas. Counterexamples in `Examples.lean` are intentional regression guards.
- Every new theorem must be added to `scripts/Audit.lean`. Keep the audit complete.
- Before claiming verification, run `python3 scripts/verify.py` or inspect successful CI for the exact head commit. Source inspection and finite computations are not Lean kernel checks.
- Pin the Lean toolchain and mathlib revision together; never silently use mathlib master.
