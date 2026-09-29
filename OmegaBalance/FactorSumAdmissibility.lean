import OmegaBalance.FactorSumFamily
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
# Local admissibility of the five-polynomial factor-sum family

This module proves the complete no-fixed-prime-divisor condition used by the
conditional Schinzel-H interface. The small primes 2,3,5,7 are handled by the
explicit residue tables in `FactorSumFamily`; primes at least 11 are handled by
the degree-nine root bound for the product polynomial.
-/

noncomputable section

namespace OmegaBalance

open Polynomial

/-- The five family polynomials over an arbitrary commutative semiring. -/
def sumFamilyPolyU (R : Type*) [CommSemiring R] : R[X] :=
  C 2 * X + C 1

def sumFamilyPolyV (R : Type*) [CommSemiring R] : R[X] :=
  C 15 * X + C 8

def sumFamilyPolyQ (R : Type*) [CommSemiring R] : R[X] :=
  C 390 * X ^ 2 + C 238 * X + C 17

def sumFamilyPolyR (R : Type*) [CommSemiring R] : R[X] :=
  C 390 * X ^ 2 + C 225 * X + C 16

def sumFamilyPolyCenter (R : Type*) [CommSemiring R] : R[X] :=
  C 23400 * X ^ 3 + C 25980 * X ^ 2 + C 8160 * X + C 511

/-- Product of the five Schinzel-family polynomials; its total degree is at most nine. -/
def sumFamilyProductPoly (R : Type*) [CommSemiring R] : R[X] :=
  sumFamilyPolyU R * sumFamilyPolyV R * sumFamilyPolyQ R *
    sumFamilyPolyR R * sumFamilyPolyCenter R

@[simp] theorem sumFamilyPolyU_eval_natCast {n t : ℕ} :
    (sumFamilyPolyU (ZMod n)).eval (t : ZMod n) = (sumFamilyU t : ZMod n) := by
  simp [sumFamilyPolyU, sumFamilyU]

@[simp] theorem sumFamilyPolyV_eval_natCast {n t : ℕ} :
    (sumFamilyPolyV (ZMod n)).eval (t : ZMod n) = (sumFamilyV t : ZMod n) := by
  simp [sumFamilyPolyV, sumFamilyV]

@[simp] theorem sumFamilyPolyQ_eval_natCast {n t : ℕ} :
    (sumFamilyPolyQ (ZMod n)).eval (t : ZMod n) = (sumFamilyQ t : ZMod n) := by
  simp [sumFamilyPolyQ, sumFamilyQ]

@[simp] theorem sumFamilyPolyR_eval_natCast {n t : ℕ} :
    (sumFamilyPolyR (ZMod n)).eval (t : ZMod n) = (sumFamilyR t : ZMod n) := by
  simp [sumFamilyPolyR, sumFamilyR]

@[simp] theorem sumFamilyPolyCenter_eval_natCast {n t : ℕ} :
    (sumFamilyPolyCenter (ZMod n)).eval (t : ZMod n) = (sumFamilyCenter t : ZMod n) := by
  simp [sumFamilyPolyCenter, sumFamilyCenter]

@[simp] theorem sumFamilyProductPoly_eval_natCast {n t : ℕ} :
    (sumFamilyProductPoly (ZMod n)).eval (t : ZMod n) =
      (sumFamilyU t : ZMod n) * sumFamilyV t * sumFamilyQ t *
        sumFamilyR t * sumFamilyCenter t := by
  simp [sumFamilyProductPoly]

/-- The product polynomial has degree at most `1+1+2+2+3=9`, in every characteristic. -/
theorem sumFamilyProductPoly_natDegree_le_nine
    (R : Type*) [CommSemiring R] :
    (sumFamilyProductPoly R).natDegree ≤ 9 := by
  unfold sumFamilyProductPoly sumFamilyPolyU sumFamilyPolyV sumFamilyPolyQ
    sumFamilyPolyR sumFamilyPolyCenter
  compute_degree

/-- For a prime modulus, the product polynomial is not the zero polynomial.

If the polynomial vanished identically modulo `ell`, then its values at 0 and 5
would show that `ell` divides both `1111936` and `393945295832825341`, whose
gcd is 1.
-/
theorem sumFamilyProductPoly_ne_zero_of_prime {ell : ℕ} (hell : ell.Prime) :
    sumFamilyProductPoly (ZMod ell) ≠ 0 := by
  letI : Fact ell.Prime := ⟨hell⟩
  intro hz
  have h0z : ((1111936 : ℕ) : ZMod ell) = 0 := by
    have h := congrArg (fun f : (ZMod ell)[X] => f.eval 0) hz
    norm_num [sumFamilyProductPoly, sumFamilyPolyU, sumFamilyPolyV, sumFamilyPolyQ,
      sumFamilyPolyR, sumFamilyPolyCenter] at h ⊢
    exact h
  have h5z : ((393945295832825341 : ℕ) : ZMod ell) = 0 := by
    have h := congrArg (fun f : (ZMod ell)[X] => f.eval 5) hz
    norm_num [sumFamilyProductPoly, sumFamilyPolyU, sumFamilyPolyV, sumFamilyPolyQ,
      sumFamilyPolyR, sumFamilyPolyCenter] at h ⊢
    exact h
  have h0d : ell ∣ 1111936 := (ZMod.natCast_eq_zero_iff _ _).mp h0z
  have h5d : ell ∣ 393945295832825341 := (ZMod.natCast_eq_zero_iff _ _).mp h5z
  have hg : ell ∣ Nat.gcd 1111936 393945295832825341 := Nat.dvd_gcd h0d h5d
  norm_num at hg
  have hell1 := hell.one_lt
  omega

/-- Every prime `ell ≥ 11` has a residue avoiding all five family factors. -/
theorem sumFamily_large_prime_admissible {ell : ℕ} (hell : ell.Prime) (hell11 : 11 ≤ ell) :
    ∃ t < ell, SumFamilyAvoidsPrime ell t := by
  letI : Fact ell.Prime := ⟨hell⟩
  let f : (ZMod ell)[X] := sumFamilyProductPoly (ZMod ell)
  have hf0 : f ≠ 0 := by
    simpa [f] using sumFamilyProductPoly_ne_zero_of_prime hell
  have hdeg : f.natDegree < Fintype.card (ZMod ell) := by
    rw [ZMod.card]
    have hle := sumFamilyProductPoly_natDegree_le_nine (ZMod ell)
    simp only [f] at hle ⊢
    omega
  have hnotall : ¬ ∀ x : ZMod ell, f.eval x = 0 := by
    intro hall
    exact hf0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      f Function.injective_id hall hdeg)
  push Not at hnotall
  obtain ⟨x, hx⟩ := hnotall
  refine ⟨x.val, x.val_lt, ?_⟩
  change (sumFamilyProductPoly (ZMod ell)).eval x ≠ 0 at hx
  rw [← ZMod.natCast_zmod_val x] at hx
  have hprod :
      (sumFamilyU x.val : ZMod ell) * sumFamilyV x.val * sumFamilyQ x.val *
        sumFamilyR x.val * sumFamilyCenter x.val ≠ 0 := by
    simpa only [sumFamilyProductPoly_eval_natCast] using hx
  have hu : (sumFamilyU x.val : ZMod ell) ≠ 0 := by
    intro hz
    apply hprod
    simp [hz]
  have hv : (sumFamilyV x.val : ZMod ell) ≠ 0 := by
    intro hz
    apply hprod
    simp [hz]
  have hq : (sumFamilyQ x.val : ZMod ell) ≠ 0 := by
    intro hz
    apply hprod
    simp [hz]
  have hr : (sumFamilyR x.val : ZMod ell) ≠ 0 := by
    intro hz
    apply hprod
    simp [hz]
  have hp : (sumFamilyCenter x.val : ZMod ell) ≠ 0 := by
    intro hz
    apply hprod
    simp [hz]
  exact ⟨
    fun hd => hu ((ZMod.natCast_eq_zero_iff _ _).2 hd),
    fun hd => hv ((ZMod.natCast_eq_zero_iff _ _).2 hd),
    fun hd => hq ((ZMod.natCast_eq_zero_iff _ _).2 hd),
    fun hd => hr ((ZMod.natCast_eq_zero_iff _ _).2 hd),
    fun hd => hp ((ZMod.natCast_eq_zero_iff _ _).2 hd)⟩

/-- Complete local admissibility: the five-polynomial family has no fixed prime divisor. -/
theorem sumFamily_prime_admissible {ell : ℕ} (hell : ell.Prime) :
    ∃ t < ell, SumFamilyAvoidsPrime ell t := by
  by_cases hsmall : ell = 2 ∨ ell = 3 ∨ ell = 5 ∨ ell = 7
  · exact sumFamily_small_prime_admissible hsmall
  · have hell11 : 11 ≤ ell := by
      by_contra h
      have hell_lt : ell < 11 := by omega
      interval_cases ell <;> norm_num at hell <;> simp_all
    exact sumFamily_large_prime_admissible hell hell11

end OmegaBalance
