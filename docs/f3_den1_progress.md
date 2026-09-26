# DEN-1 progress

PR #22 contains the candidate partial-summation bridge from weighted AP-PNT to unweighted fixed-residue prime counts, ending at `f3PrimeAPCountingReal_normalized_tendsto`.

The first exact-head build exposed a real Lean 4.34 compatibility failure inside the pinned ANT source. A minimal upstream compatibility commit adds an explicit real binder annotation; the consumer is pinned to that exact commit and is being revalidated. No DEN density theorem is marked complete before exact-head build and audits pass.


2026-09-26 compatibility note: Lean #456 failed in the pinned ANT `Consequences.lean` Liouville helper because the post-rewrite goal used Multiset count/toFinset while the helper equality used List count/primeFactors. ANT commit `099d3726c2c74841024110ec1dd9902f7ef36e9e` adds an explicit simp-normalized equality before `congrArg`; no AP/PNT statement changes. Consumer commit `40afcdbbea0315e7a3a3a3caf5435ffaacda3dae` pins that exact upstream commit for revalidation.


2026-09-26 exact-head note: consumer head `6922dad91bf4301d3bbbf6b78f4233b5f6677635` passed Lean #460 and Factor-sum #448 completely, so the unweighted AP bridge `f3PrimeAPCountingReal_normalized_tendsto` is now exact-head verified on the repository's Lean 4.34.0 / pinned mathlib tree.

The next DEN-1 layer is now in code: `f3PrimeNegLevelAPDifference k x` subtracts the residue-`1` prime counts for moduli `3^k` and `3^(k+1)`, and `f3PrimeNegLevelAPDifference_normalized_tendsto_totient` proves its normalized limit is the difference of the two Euler-totient reciprocals. This is the exact AP proxy for `F₃=-k`; it does not yet claim the simplified constant `3^(-k)` or the final equality with the F₃-filtered prime count. The theorem is registered in `scripts/Audit.lean`; its new exact head must pass the full gate before promotion.


2026-09-26 negative exact-density note: head `52600809f57835ee7e5182f09c3c72ea2eac0893`
passed Lean #526 and Factor-sum #514 completely. The real negative-level count is now
proved equal to the nested AP difference, and
`f3PrimeNegLevelCountingReal_normalized_tendsto` gives normalized constant
`1/(3:ℝ)^k` for every `k>0`. The axiom log contains 369 audited declarations and
the finite regression remains 144240 PASS.

The next candidate file `F3PrimeDensityExactPos.lean` builds the symmetric
positive-level result. Unlike the negative side, the proof deliberately includes the
prime `2` at level `+1` instead of silently deleting it; the nested `-1` residue
difference is therefore an exact finite-set identity for the actual positive-level
prime count. This candidate is not promoted until its exact head passes the full gate.


2026-09-26 positive exact-density note: head `3c93ea182cefa864b77d6fe74a55ff3cdd455485` passed Lean #530 and Factor-sum #518 completely. The exact positive-level prime count, including prime `2` at level `+1`, has normalized constant `1/(3:ℝ)^k` for every `k>0`. This head reports 377 audited declarations, 46 Lean files with no proof escape, exact audit coverage, and 144240 PASS.

The next candidate layer is `F3PrimeDensityTail.lean` on PR #22. It identifies the actual event `K ≤ |F₃(p)|` for every prime, including `p=2,3`, with the union of the `-1` and `+1` classes modulo `3^K`; proves those AP sets are disjoint; and reduces the actual tail count exactly to their sum. The target `f3PrimeTailCountingReal_normalized_tendsto` has constant `1/(3:ℝ)^(K-1)=3^(1-K)`. Source head `feea462640ff7e5582d05342d376e2de865ee9e9` contains the file, top-level import, and Audit registrations; exact-head CI is still required before promotion.


2026-09-26 DEN-1 tail exact-head note: source head `5c0ba97f7f6ffbf668a8e5ed48bdd37eaea28ea3` passed Lean #543 and Factor-sum #531 completely. Lean #543 reports 386 audited theorem declarations using only standard Lean axioms, 47 Lean source files with no proof escapes, exact 386/386 audit coverage, and 144240 finite checks PASS. Therefore the actual prime tail theorem `f3PrimeTailCountingReal_normalized_tendsto` is now verified: for every fixed `K>0`, primes with `K ≤ |F₃(p)|` have normalized density `1/(3:ℝ)^(K-1)=3^(1-K)`. Together with the already verified positive and negative exact-level theorems, DEN-1's requested `±k` and tail densities are proof-complete on the stacked branch. Main-branch integration remains separate from proof completion.
