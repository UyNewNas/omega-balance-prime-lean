# F3 progress round 17

Exact verified source SHA: `feada6b9b140a1badf9a57a80feff081fdcdb791`.

## Completed this round

The preceding stacked SHA `9303de1a53f774a809d5523d7dc45a59f2f9d1a4`
failed only at the final analytic logarithm identity because the established
output-fiber coefficient equality had the reverse orientation from the
`HasSum.congr_fun` goal.

The one-line correction uses the symmetry of
`f3PadicLogComposition_output_fiber_tsum_eq_coeff`.  The resulting public
theorems `f3PadicLogOnePlus_product` and `f3PadicLog_mul` now build on the
pinned Lean 4.34.0 / mathlib `5ed2965256430c3649e86755f9576b54eca72435`
tree.  Hence LOG-1 now includes the genuine identity

```
f3PadicLog (m * n) = f3PadicLog m + f3PadicLog n
```

under the explicit hypotheses `m,n>1`, `3∤m`, and `3∤n`.

Lean run `36276936812` on the exact SHA completed successfully: library
build, kernel regressions, axiom audit, source audit, declaration coverage,
and finite F3 regression all passed.  The log reports 492 audited project
declarations, 71 Lean source files with no proof escapes, 492/492 exact
coverage, and 144240 finite checks passing.  Factor-sum run `36276936795`
on the same SHA also succeeded.

The stacked carrier branch `feat/f3-prime-density-count-v1` was advanced by
a non-forced fast-forward to the exact verified SHA.

## RUN dependency audit

The locked mathlib and `UyNewNas/analytic-number-theory-lean` do not contain
Shiu or Banks--Freiberg--Turnage-Butterbaugh consecutive-prime strings.

Corollary 3 of arXiv:1311.7003 gives the precise required external result:
for coprime `a,D`, `D≥3`, and every `m≥2`, infinitely many strings of
`m` consecutive primes are all `a mod D`, with total span at most
`D*C_m`, where `C_m` depends only on `m`.

For `c≠0` the F3 specialization is
`D=3^(|c|+1)`, with residue `3^|c|-1` for positive `c` and
`3^|c|+1` for negative `c`.  Existing `F3Infinitude.lean` already proves
these residues are reduced and force the exact signed F3 level.

AxiomMath/PrimeGapsLib contains substantial Maynard--Tao bounded-gap
formalization, but its current main branch is pinned to Lean 4.33.0-rc1 and
mathlib `288f16d9a07189233a9bc5e1c143c38d1f3f4d37`, whereas this project uses
Lean 4.34.0 and mathlib `5ed296...`.  The inspected public witness also
closes a two-prime DHL conclusion rather than arbitrary-length consecutive
congruent-prime strings.  It is therefore not currently a drop-in dependency.

## Remaining

RUN-1 / RUN-2 and final integration to master remain open.  LOG-1 is now
theorem-complete and exact-green on the stacked source SHA.
