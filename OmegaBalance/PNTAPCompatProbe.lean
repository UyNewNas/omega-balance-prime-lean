import PrimeNumberTheoremAnd.Consequences

/-!
Compatibility probe only: the omega repository remains pinned to Lean 4.34.0
and mathlib 5ed2965.  This module checks whether the ANT snapshot can expose
its proved AP-PNT interfaces under the consumer pin without changing theorem
statements or introducing axioms.
-/

#check WeakPNT_AP
#check chebyshev_asymptotic_pnt
