# F₃ formalization progress — round 18

## Verified source head

- source commit: `386c1f33bed1a30886939de0433d2f1f8bdfde02`
- branch: `feat/f3-run-uniform-bound-v1`
- Lean Actions run: `36281970607` — success
- Factor-sum run: `36281970573` — success
- axiom audit: 511 declarations, standard Lean axioms only
- source audit: 73 Lean files, no proof escapes
- declaration coverage: 511/511 exactly once
- finite regression: 144240 PASS

## RUN-1 / RUN-2 completed local interfaces

File: `OmegaBalance/F3ConsecutivePrimeIndex.lean`.

The exact-green head proves that the BFTB span constant is uniform in the
nonzero target F₃ level: for fixed run length `L >= 2`, the witness `C`
is chosen before `c`, so `C` depends only on `L`; the target-level
dependence is the explicit factor
`f3RunModulus c = 3^(|c|+1)`.

It also combines the unconditional `L=1` case (span zero) with the
conditional `L>=2` BFTB branch, and upgrades the "for every lower bound B"
formulation to literal infinitude of start indices in the full prime
enumeration `Nat.nth Nat.Prime`.

New audited declarations:

- `f3PrimeIndexRunsBounded_uniform_of_BFTB`
- `f3PrimeIndexRunsBounded_all_lengths_of_BFTB`
- `F3PrimeIndexRunAt`
- `f3PrimeIndexRunStarts_infinite_of_arbitrarily_far`
- `f3PrimeIndexRunStarts_infinite_uniform_of_BFTB`
- `f3PrimeIndexRunStarts_infinite_all_lengths_of_BFTB`

These declarations do not assert BFTB itself. `BFTBPrimeIndexRuns` remains
only a proposition-shaped dependency, not an axiom or theorem.

## Exact remaining RUN dependency

The Banks--Freiberg--Turnage-Butterbaugh Corollary 3 reduction has been
checked against arXiv:1311.7003. Its elementary part sends an admissible
monic tuple by `b_j = D*a_j + a`, preserves admissibility and coprimality,
and scales the span by exactly `D`. The deep part is Theorem 1: a CRT
construction eliminates primes at positions outside the tuple, followed by
a maximal-subset argument and Maynard--Tao to obtain genuinely consecutive
primes.

`AxiomMath/PrimeGapsLib@1faa7b14e82ddebc2772dfb9153922f01b106477`
contains the Maynard--Tao many-primes endgame, but no BFTB consecutive-class
theorem. It is pinned to Lean 4.33.0-rc1 / mathlib
`288f16d9a07189233a9bc5e1c143c38d1f3f4d37`; this repository is pinned to
Lean 4.34.0 / mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The latter mathlib commit is a direct descendant of the former (1327 commits
ahead), so the preferred route is a narrow source-compatible adaptation,
not a toolchain downgrade.

## Candidate beyond the verified head

Branch `feat/f3-run-bftb-corollary-arith-v1`, commit
`75ef096717eee5a0381e3a4c1382d572e7753868`, adds and audits:

- `bftbAffineResidue_modEq`
- `bftbAffineResidue_coprime`
- `bftbAffine_span`
- `bftbAffine_span_le`

At the time this ledger entry is written, the exact Lean CI for that commit
is still running, so those four declarations are not yet promoted to
verified status.

## Global status

INF, COR, DEN and LOG theorem layers are present on the stacked exact-green
tree; LOG includes the genuine analytic multiplication law
`f3PadicLog_mul`. RUN remains incomplete until the BFTB/Shiu consecutive
prime theorem itself is formally derived and audited. Final stacked-to-master
integration is also still pending.
