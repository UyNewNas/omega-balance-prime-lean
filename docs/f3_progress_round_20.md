# F₃ progress round 20

Date: 2026-09-27

Working branch: `feat/f3-bftb-crt-v1`
Stacked base: `feat/f3-bftb-admissibility-v1`
Master observed at `0e60cc57d5a04f095ecfdda3697be94ea7e35a16`.

## Exact verified source

SHA `408bfa4189d39ee480634596ad8820ad6c40d343`

- Lean run 36287556973: completed / success
- Factor-sum run 36287556952: completed / success
- library build: PASS
- kernel regressions: PASS
- axiom audit: 527 declarations; standard Lean axioms only
- source audit: 76 Lean files; no proof escapes
- audit coverage: 527/527 exactly once
- finite F₃ regression: 144240 PASS

## New files and theorems

`OmegaBalance/F3BFTBCRT.lean`
- `bftb_exists_crt_residue`
- `bftb_exists_crt_shift`
- `bftb_exists_crt_shift_of_large_moduli`

`OmegaBalance/F3BFTBAuxPrimes.lean`
- `bftbAuxPrime_prime`
- `bftbAuxPrime_lower_bound`
- `bftbAuxPrime_injective`
- `bftbAuxPrime_pairwise_coprime`
- `exists_bftbAuxPrime_family_gt`
- `bftbAuxPrime_coprime_of_lt`
- `bftb_exists_crt_shift_from_bound`

These close the finite auxiliary-prime selection and Chinese-remainder step corresponding to equations (2) and (3) in the proof of BFTB Theorem 1. From a common bound on the coefficient and all finite offsets, the final theorem chooses successive auxiliary primes above the bound, proves the required primality/coprimality properties, and obtains one shift with the required divisibility and protected-offset nondivisibility conclusions.

## Repair history

Candidate SHA `9660bd8eea13d0b53afe64a0a20114ac037c394d` failed the library build because a helper data definition used `Nat.nth`. The helper was eliminated; the theorem interfaces now use `Nat.nth Nat.Prime` directly. Repaired SHA `6b6a9a3cd574b98db1d923b1f51e18a54d0cb3c0` passed all gates, then `408bfa...` added the bound-to-CRT package and also passed all gates.

## Remaining RUN work

1. Concrete interval complement `S`, product `Q`, and persistence of the forced divisors for `g*(Q*N+A)+t`.
2. Admissibility and side conditions for the transformed tuple.
3. Trusted Maynard--Tao many-primes input compatible with the pinned toolchain.
4. Maximal-subset argument upgrading many-primes to genuinely consecutive primes.
5. Corollary 3 instantiation, F₃ transfer, final stacked integration.

A stacked draft PR was not created in this round; the working branch and exact verified commits are present on GitHub.
