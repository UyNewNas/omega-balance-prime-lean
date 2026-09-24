import OmegaBalance.FactorSumIrreducible
import OmegaBalance.FactorSumLowCount

/-!
# Conditional Schinzel-H interface for the factor-sum family

This file does **not** prove Schinzel's hypothesis and does not introduce it as
an axiom.  `SumFamilySchinzelH` is the exact external implication needed for
this fixed five-polynomial family: irreducibility plus local admissibility imply
infinitely many simultaneous prime values.  The two antecedents are discharged
by the kernel-checked theorems in `FactorSumIrreducible` and
`FactorSumAdmissibility`; only the Schinzel implication itself remains an
explicit theorem hypothesis.
-/

noncomputable section

namespace OmegaBalance

/-- The specialized instance of Schinzel H used by this project.

Keeping the implication itself as data makes the trust boundary explicit: the
repository proves the two structural inputs, but does not claim this external
infinitude principle unconditionally. -/
def SumFamilySchinzelH : Prop :=
  (Irreducible (sumFamilyPolyU ℚ) ∧
    Irreducible (sumFamilyPolyV ℚ) ∧
    Irreducible (sumFamilyPolyQ ℚ) ∧
    Irreducible (sumFamilyPolyR ℚ) ∧
    Irreducible (sumFamilyPolyCenter ℚ)) →
  (∀ ell : ℕ, ell.Prime → ∃ t < ell, SumFamilyAvoidsPrime ell t) →
  Set.Infinite {t : ℕ | SumFamilyPrimeValues t}

/-- Under the explicit specialized Schinzel-H premise, the five family values
are simultaneously prime for infinitely many natural parameters. -/
theorem sumFamily_infinite_of_schinzelH (hH : SumFamilySchinzelH) :
    Set.Infinite {t : ℕ | SumFamilyPrimeValues t} := by
  unfold SumFamilySchinzelH at hH
  exact hH sumFamily_five_irreducible_rat (fun _ hell => sumFamily_prime_admissible hell)

/-- Schinzel H for this fixed family therefore supplies infinitely many
S-balanced prime centres at total multiplicity count `TΩ = 9`. -/
theorem sumFamily_level_nine_infinite_of_schinzelH (hH : SumFamilySchinzelH) :
    Set.Infinite {p : ℕ | IsPrimeFactorSumBalancedPrime p ∧ omegaSum p = 9} :=
  infinite_sumFamily_implies_level_nine (sumFamily_infinite_of_schinzelH hH)

/-- Conditional optimality statement: under the explicit Schinzel-H premise,
level `9` occurs infinitely often, while every fixed total-count stratum that
occurs infinitely often is at least `9`.

This is the formal meaning of “under Schinzel H, the minimum fixed `TΩ` that
can occur infinitely often is exactly `9`”. -/
theorem sumBalanced_minimum_infinite_level_of_schinzelH (hH : SumFamilySchinzelH) :
    Set.Infinite {p : ℕ | IsPrimeFactorSumBalancedPrime p ∧ omegaSum p = 9} ∧
      ∀ k : ℕ,
        Set.Infinite {p : ℕ | IsPrimeFactorSumBalancedPrime p ∧ omegaSum p = k} → 9 ≤ k := by
  refine ⟨sumFamily_level_nine_infinite_of_schinzelH hH, ?_⟩
  intro k hk
  exact infinite_sumBalanced_level_ge_nine hk

end OmegaBalance
