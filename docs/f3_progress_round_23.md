# F3 formalization progress — round 23

Verified source: ad664ee952d33b5b95254e83a4b4aefea013d81d.

Lean run 36295318758: success.
Factor-sum run 36295318760: success.
Axiom audit: 550 declarations, standard Lean axioms only.
Source audit: 82 Lean files, no proof escapes.
Audit coverage: 550/550 exactly once.
Finite regression: 144240 PASS.

New verified theorems:
- bftb_exact_prime_pattern_extend
- bftb_consecutivePrimes_of_exact_affine_offset_interval
- bftb_consecutivePrimes_of_tuple_pattern_and_outside
- bftb_indexed_many_primes_to_finset

Dependency review: PrimeGapsLib's many-primes theorem still takes Bombieri-Vinogradov as a hypothesis. The pinned analytic-number-theory dependency documents that its current theorem is not the classical uniform average Bombieri-Vinogradov theorem. A stronger unconditional Standard BV endpoint exists in the Liu-Wang source tree, but that source uses an older Lean/mathlib pin and therefore needs compatibility and trust auditing before reuse.

Remaining RUN work: finish the finite selected-set to consecutive-block bridge, port a fully proved many-primes producer, assemble the consecutive residue-class theorem, specialize to all nonzero F3 levels, then integrate to master after exact verification.
