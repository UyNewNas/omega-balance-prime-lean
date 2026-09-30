# F3 LOG-1 progress

## 2026-09-26

Exact head `604e1d43f33de2022c2eab54ad55f8777d1c9d83` passed Lean run
`36240073017` and Factor-sum run `36240072894`.

Completed in `OmegaBalance/F3PadicLogDomain.lean`:

- `f3PadicUnit_mul`
- `f3PadicDelta_eq_intCast`
- `f3PadicDelta_valuation`
- `f3PadicDelta_ne_zero`
- `f3PadicDelta_norm`
- `f3PadicDelta_norm_lt_one`

For `n > 1` and `3 ∤ n`, the embedded coordinate `U(n)` satisfies
`valuation (U(n)-1) = |F3(n)|` and `norm (U(n)-1) = 3^(-|F3(n)|) < 1`.

This is a genuine p-adic domain/isometry pre-layer only. Remaining LOG-1 work:
construct the convergent p-adic logarithm on the pinned mathlib revision, prove the
multiplicative homomorphism on the principal-unit domain, prove valuation preservation,
and derive the signed F3/log formula. No integer coordinate is renamed as a logarithm.
