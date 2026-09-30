# F₃ progress round 21

Date: 2026-09-27

Working branch: `feat/f3-bftb-crt-shift-v1`
Parent exact-green source: `408bfa4189d39ee480634596ad8820ad6c40d343`.

## This round

Adds the next finite BFTB CRT layer:

- a proper prime divisor implies compositeness;
- a finite CRT divisor family yields compositeness once properness is known;
- every assigned auxiliary modulus divides the finite product of the moduli;
- replacing `A` by `A + (∏ q_t) N` preserves every forced divisor;
- the same product shift preserves every protected nondivisibility condition.

This isolates the remaining size argument from the congruence argument.  The next
finite step is to choose an explicit positive multiplier (e.g. 2) and prove all
assigned auxiliary primes are strictly smaller than the shifted excluded values.

No BFTB/Maynard--Tao consecutive-prime theorem is assumed or added as an axiom.
## Exact verification

Source SHA: `e9dfe940ce511005b5fdabaaffe1d0befc5372e4`

- Lean push run 36289378419: completed / success
- Factor-sum push run 36289378391: completed / success
- library build: PASS
- kernel regression: PASS
- axiom audit: 532 declarations; only standard Lean axioms
- source audit: 77 Lean files; no proof escapes
- audit coverage: 532/532 exactly once
- finite F₃ regression: 144240 PASS

This SHA is the exact verified source for the five new CRT-shift theorems above.
