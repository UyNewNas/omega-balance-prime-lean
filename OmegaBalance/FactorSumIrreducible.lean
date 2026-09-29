import OmegaBalance.FactorSumAdmissibility
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ReduceModChar

/-!
# Irreducibility of the five-polynomial factor-sum family

The two linear factors are irreducible over `ℚ` by degree.  For the two
quadratics and the cubic centre we prove absence of rational roots.  The
quadratic fingerprints agree with the research discriminants `30124` and
`25665`; computationally, the no-root certificates are carried out after the
standard leading-coefficient scaling, modulo `7` for the quadratics and modulo
`19` for the cubic.  The scaling produces a monic integral polynomial, so the
integral-root theorem reduces a hypothetical rational root to an integer root.
-/

noncomputable section

namespace OmegaBalance

open Polynomial

/-- First quadratic discriminant recorded in the research note. -/
theorem sumFamilyQ_discriminant :
    (238 : ℤ) ^ 2 - 4 * 390 * 17 = 30124 := by
  norm_num

/-- Second quadratic discriminant recorded in the research note. -/
theorem sumFamilyR_discriminant :
    (225 : ℤ) ^ 2 - 4 * 390 * 16 = 25665 := by
  norm_num

/-- `30124 ≡ 3 (mod 7)`, and `3` is not a square modulo `7`. -/
theorem sumFamilyQ_discriminant_not_square_mod_seven :
    ¬ ∃ z : ZMod 7, z ^ 2 = (30124 : ZMod 7) := by
  decide

/-- `25665 ≡ 3 (mod 7)`, and `3` is not a square modulo `7`. -/
theorem sumFamilyR_discriminant_not_square_mod_seven :
    ¬ ∃ z : ZMod 7, z ^ 2 = (25665 : ZMod 7) := by
  decide

/-- The first linear member is irreducible over the rationals. -/
theorem sumFamilyPolyU_irreducible_rat :
    Irreducible (sumFamilyPolyU ℚ) := by
  apply Polynomial.irreducible_of_degree_eq_one
  unfold sumFamilyPolyU
  compute_degree!

/-- The second linear member is irreducible over the rationals. -/
theorem sumFamilyPolyV_irreducible_rat :
    Irreducible (sumFamilyPolyV ℚ) := by
  apply Polynomial.irreducible_of_degree_eq_one
  unfold sumFamilyPolyV
  compute_degree!

/-- The quadratic `390 X² + 238 X + 17` is irreducible over `ℚ`.

A root `x` would make `y = 390x` a root of the monic integral polynomial
`y² + 238y + 6630`.  Hence `y` is an integer.  Reduction modulo `7` would then
give `y² + 1 = 0`, which has no solution. -/
theorem sumFamilyPolyQ_irreducible_rat :
    Irreducible (sumFamilyPolyQ ℚ) := by
  have hdeg : (sumFamilyPolyQ ℚ).natDegree = 2 := by
    unfold sumFamilyPolyQ
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdeg]
  · intro x hx
    have hx0 : (390 : ℚ) * x ^ 2 + 238 * x + 17 = 0 := by
      simpa [Polynomial.IsRoot.def, sumFamilyPolyQ] using hx
    let g : ℤ[X] := X ^ 2 + C 238 * X + C 6630
    have hgmonic : g.Monic := by
      dsimp [g]
      simp only [add_assoc]
      apply monic_X_pow_add
      compute_degree!
    have hgy0 : ((390 : ℚ) * x) ^ 2 + 238 * ((390 : ℚ) * x) + 6630 = 0 := by
      calc
        ((390 : ℚ) * x) ^ 2 + 238 * ((390 : ℚ) * x) + 6630 =
            390 * ((390 : ℚ) * x ^ 2 + 238 * x + 17) := by ring
        _ = 0 := by rw [hx0]; norm_num
    have hgy : aeval ((390 : ℚ) * x) g = 0 := by
      simpa [g, aeval_def] using hgy0
    obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hgmonic hgy
    have hzq : (z : ℚ) ^ 2 + 238 * (z : ℚ) + 6630 = 0 := by
      rw [hz] at hgy
      simpa [g, aeval_def] using hgy
    have hzi : z ^ 2 + 238 * z + 6630 = 0 := by
      exact_mod_cast hzq
    have hzmod := congrArg (Int.castRingHom (ZMod 7)) hzi
    norm_num [map_add, map_mul, map_pow] at hzmod
    reduce_mod_char at hzmod
    have hno : ∀ w : ZMod 7, w ^ 2 + 1 ≠ 0 := by decide
    exact hno (z : ZMod 7) hzmod

/-- The quadratic `390 X² + 225 X + 16` is irreducible over `ℚ`.

After `y = 390x`, a rational root becomes an integer root of
`y² + 225y + 6240`; modulo `7` this is `y² + y + 3`, which has no root. -/
theorem sumFamilyPolyR_irreducible_rat :
    Irreducible (sumFamilyPolyR ℚ) := by
  have hdeg : (sumFamilyPolyR ℚ).natDegree = 2 := by
    unfold sumFamilyPolyR
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdeg]
  · intro x hx
    have hx0 : (390 : ℚ) * x ^ 2 + 225 * x + 16 = 0 := by
      simpa [Polynomial.IsRoot.def, sumFamilyPolyR] using hx
    let g : ℤ[X] := X ^ 2 + C 225 * X + C 6240
    have hgmonic : g.Monic := by
      dsimp [g]
      simp only [add_assoc]
      apply monic_X_pow_add
      compute_degree!
    have hgy0 : ((390 : ℚ) * x) ^ 2 + 225 * ((390 : ℚ) * x) + 6240 = 0 := by
      calc
        ((390 : ℚ) * x) ^ 2 + 225 * ((390 : ℚ) * x) + 6240 =
            390 * ((390 : ℚ) * x ^ 2 + 225 * x + 16) := by ring
        _ = 0 := by rw [hx0]; norm_num
    have hgy : aeval ((390 : ℚ) * x) g = 0 := by
      simpa [g, aeval_def] using hgy0
    obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hgmonic hgy
    have hzq : (z : ℚ) ^ 2 + 225 * (z : ℚ) + 6240 = 0 := by
      rw [hz] at hgy
      simpa [g, aeval_def] using hgy
    have hzi : z ^ 2 + 225 * z + 6240 = 0 := by
      exact_mod_cast hzq
    have hzmod := congrArg (Int.castRingHom (ZMod 7)) hzi
    norm_num [map_add, map_mul, map_pow] at hzmod
    reduce_mod_char at hzmod
    have hno : ∀ w : ZMod 7, w ^ 2 + w + 3 ≠ 0 := by decide
    exact hno (z : ZMod 7) hzmod

/-- The centre cubic has no root modulo `19` after monic scaling. -/
theorem sumFamilyCenter_scaled_no_root_mod_nineteen :
    ∀ w : ZMod 19, w ^ 3 + 7 * w ^ 2 + 4 * w + 5 ≠ 0 := by
  decide

/-- The cubic centre polynomial is irreducible over `ℚ`.

For a hypothetical rational root `x`, put `y = 23400x`.  Then `y` is a root
of the monic integral polynomial
`y³ + 25980y² + (23400·8160)y + 23400²·511`.  Thus `y` is integral, while
its reduction modulo `19` would violate the preceding finite certificate. -/
theorem sumFamilyPolyCenter_irreducible_rat :
    Irreducible (sumFamilyPolyCenter ℚ) := by
  have hdeg : (sumFamilyPolyCenter ℚ).natDegree = 3 := by
    unfold sumFamilyPolyCenter
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdeg]
  · intro x hx
    have hx0 :
        (23400 : ℚ) * x ^ 3 + 25980 * x ^ 2 + 8160 * x + 511 = 0 := by
      simpa [Polynomial.IsRoot.def, sumFamilyPolyCenter] using hx
    let g : ℤ[X] :=
      X ^ 3 + C 25980 * X ^ 2 + C (23400 * 8160) * X + C (23400 ^ 2 * 511)
    have hgmonic : g.Monic := by
      dsimp [g]
      simp only [add_assoc]
      apply monic_X_pow_add
      compute_degree!
    have hgy0 :
        ((23400 : ℚ) * x) ^ 3 + 25980 * ((23400 : ℚ) * x) ^ 2 +
          190944000 * ((23400 : ℚ) * x) + 279803160000 = 0 := by
      calc
        ((23400 : ℚ) * x) ^ 3 + 25980 * ((23400 : ℚ) * x) ^ 2 +
            190944000 * ((23400 : ℚ) * x) + 279803160000 =
          (23400 : ℚ) ^ 2 *
            ((23400 : ℚ) * x ^ 3 + 25980 * x ^ 2 + 8160 * x + 511) := by ring
        _ = 0 := by rw [hx0]; ring
    have hgy : aeval ((23400 : ℚ) * x) g = 0 := by
      simpa [g, aeval_def] using hgy0
    obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hgmonic hgy
    have hzq :
        (z : ℚ) ^ 3 + 25980 * (z : ℚ) ^ 2 + 190944000 * (z : ℚ) +
          279803160000 = 0 := by
      rw [hz] at hgy
      simpa [g, aeval_def] using hgy
    have hzi :
        z ^ 3 + 25980 * z ^ 2 + 190944000 * z + 279803160000 = 0 := by
      exact_mod_cast hzq
    have hzmod := congrArg (Int.castRingHom (ZMod 19)) hzi
    norm_num [map_add, map_mul, map_pow] at hzmod
    reduce_mod_char at hzmod
    exact sumFamilyCenter_scaled_no_root_mod_nineteen (z : ZMod 19) hzmod

/-- All five family members are irreducible over `ℚ`. -/
theorem sumFamily_five_irreducible_rat :
    Irreducible (sumFamilyPolyU ℚ) ∧
    Irreducible (sumFamilyPolyV ℚ) ∧
    Irreducible (sumFamilyPolyQ ℚ) ∧
    Irreducible (sumFamilyPolyR ℚ) ∧
    Irreducible (sumFamilyPolyCenter ℚ) := by
  exact ⟨sumFamilyPolyU_irreducible_rat, sumFamilyPolyV_irreducible_rat,
    sumFamilyPolyQ_irreducible_rat, sumFamilyPolyR_irreducible_rat,
    sumFamilyPolyCenter_irreducible_rat⟩

end OmegaBalance
