# F₃ formalization progress — round 18 affine verification addendum

The candidate recorded in `docs/f3_progress_round_18.md` is now verified.

- exact source commit: `75ef096717eee5a0381e3a4c1382d572e7753868`
- branch: `feat/f3-run-bftb-corollary-arith-v1`
- Lean run: `36282153196` — completed / success
- Factor-sum run: `36282153189` — completed / success
- axiom audit: 515 declarations, standard Lean axioms only
- source audit: 73 Lean files, no proof escapes
- declaration coverage: 515/515 exactly once
- finite regression: 144240 PASS

New verified elementary BFTB Corollary 3 interfaces:

- `bftbAffineResidue_modEq`: every value `D*n + (D*t+a)` is congruent to `a` modulo `D`.
- `bftbAffineResidue_coprime`: if `a` and `D` are coprime then every affine offset `D*t+a` is coprime to `D`.
- `bftbAffine_span`: endpoint spans scale exactly by `D`.
- `bftbAffine_span_le`: a base span bound `C` becomes the quantitative bound `D*C`.

This closes the elementary residue/coprime/span arithmetic in the published
Corollary 3 reduction. It does not prove `BFTBPrimeIndexRuns`; the remaining
deep dependency is the admissibility-preservation and Theorem-1
CRT/maximal-subset/Maynard--Tao consecutive-prime mechanism.
