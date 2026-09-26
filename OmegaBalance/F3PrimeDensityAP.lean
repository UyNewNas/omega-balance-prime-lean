import OmegaBalance.F3PrimeDensityResidues
import PrimeNumberTheoremAnd.Consequences

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

/-- Weighted prime sum in one fixed arithmetic progression. -/
noncomputable def f3ThetaAP (A a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Icc 0 ⌊x⌋₊).filter Nat.Prime,
    if p % A = a then Real.log p else 0

/-- Unweighted prime count in one fixed arithmetic progression. -/
noncomputable def f3PrimeAPCountingReal (A a : ℕ) (x : ℝ) : ℝ :=
  (((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p % A = a).card : ℝ)

end OmegaBalance
