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
Exact verification status must be filled from CI for the source SHA produced by
this round.
