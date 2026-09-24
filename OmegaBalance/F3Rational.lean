import OmegaBalance.F3Arithmetic
import Mathlib.Tactic.FieldSimp

/-!
# Rational F₃ and the Cayley-conjugate operation

Functions are totalized as in mathlib. Theorems about the ordinary rational
valuation explicitly exclude x = ±1 and zero denominators. The semigroup
statements use x > 1, so all intermediate values remain in the same domain.
No assertion says that the operation preserves integers or primes.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

def f3Rat (x : ℚ) : ℤ := padicValRat 3 (x + 1) - padicValRat 3 (x - 1)

def f3Cayley (x : ℚ) : ℚ := (x + 1) / (x - 1)

def f3Star (x y : ℚ) : ℚ := (x * y + 1) / (x + y)

/-- Compatibility with the integer extension, including its totalized values. -/
theorem f3Rat_int (z : ℤ) : f3Rat (z : ℚ) = f3Int z := by
  have hp : (z : ℚ) + 1 = ((z + 1 : ℤ) : ℚ) := by push_cast; rfl
  have hm : (z : ℚ) - 1 = ((z - 1 : ℤ) : ℚ) := by push_cast; rfl
  rw [f3Rat, hp, hm, ← v3Int_eq_padicValRat, ← v3Int_eq_padicValRat]
  rfl

theorem f3Rat_nat {n : ℕ} (hn : 1 ≤ n) : f3Rat (n : ℚ) = f3 n := by
  have h := f3Rat_int (n : ℤ)
  simpa only [Int.cast_natCast, f3Int_nat hn] using h

theorem f3Rat_neg (x : ℚ) : f3Rat (-x) = -f3Rat x := by
  have hp : -x + 1 = -(x - 1) := by ring
  have hm : -x - 1 = -(x + 1) := by ring
  simp only [f3Rat, hp, hm, padicValRat.neg]
  ring

/-- F₃ is the valuation of its Cayley coordinate. -/
theorem f3Rat_eq_cayley_valuation {x : ℚ} (hp : x + 1 ≠ 0) (hm : x - 1 ≠ 0) :
    f3Rat x = padicValRat 3 (f3Cayley x) := by
  rw [f3Cayley, padicValRat.div hp hm]
  rfl

theorem f3Star_comm (x y : ℚ) : f3Star x y = f3Star y x := by
  simp only [f3Star, mul_comm, add_comm]

theorem f3Star_gt_one {x y : ℚ} (hx : 1 < x) (hy : 1 < y) :
    1 < f3Star x y := by
  rw [f3Star, lt_div_iff₀ (by linarith : 0 < x + y)]
  have := mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)
  nlinarith

theorem f3Star_add_one {x y : ℚ} (hs : x + y ≠ 0) :
    f3Star x y + 1 = (x + 1) * (y + 1) / (x + y) := by
  unfold f3Star
  field_simp
  <;> ring

theorem f3Star_sub_one {x y : ℚ} (hs : x + y ≠ 0) :
    f3Star x y - 1 = (x - 1) * (y - 1) / (x + y) := by
  unfold f3Star
  field_simp
  <;> ring

/-- Exact additivity on every nonsingular rational input, not only positive ones. -/
theorem f3Rat_star {x y : ℚ} (hxp : x + 1 ≠ 0) (hxm : x - 1 ≠ 0)
    (hyp : y + 1 ≠ 0) (hym : y - 1 ≠ 0) (hs : x + y ≠ 0) :
    f3Rat (f3Star x y) = f3Rat x + f3Rat y := by
  rw [f3Rat, f3Star_add_one hs, f3Star_sub_one hs,
    padicValRat.div (mul_ne_zero hxp hyp) hs,
    padicValRat.div (mul_ne_zero hxm hym) hs,
    padicValRat.mul hxp hyp, padicValRat.mul hxm hym]
  unfold f3Rat
  ring

theorem f3Rat_star_of_gt_one {x y : ℚ} (hx : 1 < x) (hy : 1 < y) :
    f3Rat (f3Star x y) = f3Rat x + f3Rat y :=
  f3Rat_star (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

theorem f3Cayley_gt_one {x : ℚ} (hx : 1 < x) : 1 < f3Cayley x := by
  rw [f3Cayley, lt_div_iff₀ (sub_pos.mpr hx)]
  linarith

theorem f3Cayley_involution {x : ℚ} (hx : 1 < x) :
    f3Cayley (f3Cayley x) = x := by
  have hm : x - 1 ≠ 0 := by linarith
  unfold f3Cayley
  field_simp
  <;> ring

theorem f3Cayley_injective {x y : ℚ} (hx : 1 < x) (hy : 1 < y)
    (h : f3Cayley x = f3Cayley y) : x = y := by
  have hh := congrArg f3Cayley h
  rwa [f3Cayley_involution hx, f3Cayley_involution hy] at hh

theorem f3Cayley_star {x y : ℚ} (hx : 1 < x) (hy : 1 < y) :
    f3Cayley (f3Star x y) = f3Cayley x * f3Cayley y := by
  have hs : x + y ≠ 0 := by linarith
  rw [f3Cayley, f3Star_add_one hs, f3Star_sub_one hs]
  have hxm : x - 1 ≠ 0 := by linarith
  have hym : y - 1 ≠ 0 := by linarith
  unfold f3Cayley
  field_simp
  <;> ring

theorem f3Star_assoc {x y z : ℚ} (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) :
    f3Star (f3Star x y) z = f3Star x (f3Star y z) := by
  apply f3Cayley_injective (f3Star_gt_one (f3Star_gt_one hx hy) hz)
    (f3Star_gt_one hx (f3Star_gt_one hy hz))
  rw [f3Cayley_star (f3Star_gt_one hx hy) hz,
    f3Cayley_star hx (f3Star_gt_one hy hz), f3Cayley_star hx hy,
    f3Cayley_star hy hz, mul_assoc]

end OmegaBalance
