# DEN-1 progress

PR #22 contains the candidate partial-summation bridge from weighted AP-PNT to unweighted fixed-residue prime counts, ending at `f3PrimeAPCountingReal_normalized_tendsto`.

The first exact-head build exposed a real Lean 4.34 compatibility failure inside the pinned ANT source. A minimal upstream compatibility commit adds an explicit real binder annotation; the consumer is pinned to that exact commit and is being revalidated. No DEN density theorem is marked complete before exact-head build and audits pass.


2026-09-26 compatibility note: Lean #456 failed in the pinned ANT `Consequences.lean` Liouville helper because the post-rewrite goal used Multiset count/toFinset while the helper equality used List count/primeFactors. ANT commit `099d3726c2c74841024110ec1dd9902f7ef36e9e` adds an explicit simp-normalized equality before `congrArg`; no AP/PNT statement changes. Consumer commit `40afcdbbea0315e7a3a3a3caf5435ffaacda3dae` pins that exact upstream commit for revalidation.
