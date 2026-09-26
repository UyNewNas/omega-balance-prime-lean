# DEN-1 progress

PR #22 contains the candidate partial-summation bridge from weighted AP-PNT to unweighted fixed-residue prime counts, ending at `f3PrimeAPCountingReal_normalized_tendsto`.

The first exact-head build exposed a real Lean 4.34 compatibility failure inside the pinned ANT source. A minimal upstream compatibility commit adds an explicit real binder annotation; the consumer is pinned to that exact commit and is being revalidated. No DEN density theorem is marked complete before exact-head build and audits pass.


2026-09-26 compatibility note: Lean #456 failed in the pinned ANT `Consequences.lean` Liouville helper because the post-rewrite goal used Multiset count/toFinset while the helper equality used List count/primeFactors. ANT commit `099d3726c2c74841024110ec1dd9902f7ef36e9e` adds an explicit simp-normalized equality before `congrArg`; no AP/PNT statement changes. Consumer commit `40afcdbbea0315e7a3a3a3caf5435ffaacda3dae` pins that exact upstream commit for revalidation.

2026-09-26 exact-head bridge note: PR #22 head `6922dad91bf4301d3bbbf6b78f4233b5f6677635` passed both Lean and Factor-sum workflows. The next stacked branch adds power-of-three AP count differences for exact valuation layers and simplifies the limiting constant to `1 / 3^k`; these are still AP-difference counts, not yet the final `F₃` event-count theorem.

The stacked exact-level branch also adds all-prime residue characterizations for the actual F3 events. The small primes 2 and 3 are handled explicitly, so the later counting identity does not need to hide a finite exceptional correction.

The next candidate layer defines the actual exact-level prime counting functions and proves, by an exact nested-finset difference, that they equal the corresponding two AP counts. It then transfers the AP asymptotic to the actual events `F3(p)=+k` and `F3(p)=-k`, each with normalized limit `1/3^k`. These declarations remain candidate until this exact tree passes Lean build, axiom, source and audit-coverage gates.

CI repair: Lean run #36221940127 failed only at the negative ModEq wrapper because `omega` cannot use primality as an arithmetic hypothesis to infer `1 ≤ p`. The repair feeds `hp.two_le` explicitly; theorem statements are unchanged.

Static follow-up repair before the next gate: the first LevelCounts Git object had its finset set-difference backslash lost while serializing the source, and the negative nested-residue inclusion repeated the same `omega`/primality lower-bound issue. Both are repaired without changing any theorem statement.
