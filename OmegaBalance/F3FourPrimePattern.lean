import OmegaBalance.F3Powers
import Mathlib.Data.Nat.ModEq

/-!
# The local seven-value pattern in F3-PAT-1

This module proves PAT-L1--PAT-L3 of the audited four-prime construction.
The residue conditions determine the seven F₃ values without any primality
assumption. They do not prove that the four points are simultaneously prime,
or that there are infinitely many prime configurations.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The four points with offsets `0, 38, 92, 146`, in that order. -/
def f3Pat1Point (n d : ℕ) (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => n
  | 1 => n + 38 * d
  | 2 => n + 92 * d
  | _ => n + 146 * d

/-- The seven signed values, independent of whether any point is prime. -/
def F3Pat1Pattern (n d : ℕ) : Prop :=
  f3 (f3Pat1Point n d 0) = 1 ∧
  f3 (f3Pat1Point n d 1) = -1 ∧
  f3 (f3Pat1Point n d 2) = -1 ∧
  f3 (f3Pat1Point n d 3) = -1 ∧
  f3 (f3Pat1Point n d 0 * f3Pat1Point n d 1) = 3 ∧
  f3 (f3Pat1Point n d 0 * f3Pat1Point n d 2) = 5 ∧
  f3 (f3Pat1Point n d 0 * f3Pat1Point n d 3) = 3

/-- The full finite configuration. This definition asserts no existence result. -/
def F3Pat1PrimeConfiguration (n d : ℕ) : Prop :=
  1 < n ∧ 0 < d ∧ (∀ i : Fin 4, (f3Pat1Point n d i).Prime) ∧
    F3Pat1Pattern n d

/-- PAT-L1: a congruence deeper than an exact valuation preserves that valuation.
Both arguments are nonzero because `v3 0` is totalized to zero. -/
theorem v3_eq_of_modEq_pow_of_lt {A B R : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hmod : A ≡ B [MOD 3 ^ R]) (hdepth : v3 B < R) : v3 A = v3 B := by
  have hdivA (k : ℕ) : 3 ^ k ∣ A ↔ k ≤ v3 A := by
    rw [v3_eq_padic]
    exact padicValNat_dvd_iff_le hA
  have hdivB (k : ℕ) : 3 ^ k ∣ B ↔ k ≤ v3 B := by
    rw [v3_eq_padic]
    exact padicValNat_dvd_iff_le hB
  apply Nat.le_antisymm
  · by_contra hle
    have hnext : 3 ^ (v3 B + 1) ∣ A := (hdivA _).mpr (by omega)
    have hnextB : 3 ^ (v3 B + 1) ∣ B :=
      (hmod.dvd_iff (pow_dvd_pow 3 (by omega : v3 B + 1 ≤ R))).mp hnext
    have := (hdivB _).mp hnextB
    omega
  · apply (hdivA _).mp
    exact (hmod.dvd_iff (pow_dvd_pow 3 (Nat.le_of_lt hdepth))).mpr
      ((hdivB _).mpr le_rfl)

/-- PAT-L2: the four point representatives modulo `729`. -/
theorem f3_pat1_point_mod729 {n d : ℕ}
    (hn : n ≡ 5 [MOD 729]) (hd : d ≡ 1 [MOD 729]) :
    f3Pat1Point n d 0 ≡ 5 [MOD 729] ∧
    f3Pat1Point n d 1 ≡ 43 [MOD 729] ∧
    f3Pat1Point n d 2 ≡ 97 [MOD 729] ∧
    f3Pat1Point n d 3 ≡ 151 [MOD 729] := by
  change n ≡ 5 [MOD 729] ∧ n + 38 * d ≡ 43 [MOD 729] ∧
    n + 92 * d ≡ 97 [MOD 729] ∧ n + 146 * d ≡ 151 [MOD 729]
  refine ⟨hn, ?_, ?_, ?_⟩
  · simpa using hn.add (hd.mul_left 38)
  · simpa using hn.add (hd.mul_left 92)
  · simpa using hn.add (hd.mul_left 146)

/-- PAT-L2: product-plus-one representatives; `756` deliberately need not be reduced. -/
theorem f3_pat1_product_add_one_mod729 {n d : ℕ}
    (hn : n ≡ 5 [MOD 729]) (hd : d ≡ 1 [MOD 729]) :
    f3Pat1Point n d 0 * f3Pat1Point n d 1 + 1 ≡ 216 [MOD 729] ∧
    f3Pat1Point n d 0 * f3Pat1Point n d 2 + 1 ≡ 486 [MOD 729] ∧
    f3Pat1Point n d 0 * f3Pat1Point n d 3 + 1 ≡ 756 [MOD 729] := by
  obtain ⟨h0, h1, h2, h3⟩ := f3_pat1_point_mod729 hn hd
  refine ⟨?_, ?_, ?_⟩
  · simpa using (h0.mul h1).add_right 1
  · simpa using (h0.mul h2).add_right 1
  · simpa using (h0.mul h3).add_right 1

/-- PAT-L3: the specified residue classes force all seven exact signed values.
The positivity assumptions are retained, and no primality hypothesis is needed. -/
theorem f3_pat1_pattern_of_mod729 {n d : ℕ} (hn : 1 < n) (hd : 0 < d)
    (hnmod : n ≡ 5 [MOD 729]) (hdmod : d ≡ 1 [MOD 729]) :
    F3Pat1Pattern n d := by
  have hunit (e c : ℕ) (hc : c ≠ 0) (hc3 : ¬ 3 ∣ c) :
      v3 (3 ^ e * c) = e := by
    rw [v3_mul (pow_ne_zero _ (by decide)) hc, v3_pow_three,
      v3_eq_zero_of_not_dvd hc3, Nat.add_zero]
  have hv6 : v3 6 = 1 := by
    simpa using hunit 1 2 (by norm_num) (by norm_num)
  have hv42 : v3 42 = 1 := by
    simpa using hunit 1 14 (by norm_num) (by norm_num)
  have hv96 : v3 96 = 1 := by
    simpa using hunit 1 32 (by norm_num) (by norm_num)
  have hv150 : v3 150 = 1 := by
    simpa using hunit 1 50 (by norm_num) (by norm_num)
  have hv216 : v3 216 = 3 := by
    simpa using hunit 3 8 (by norm_num) (by norm_num)
  have hv486 : v3 486 = 5 := by
    simpa using hunit 5 2 (by norm_num) (by norm_num)
  have hv756 : v3 756 = 3 := by
    simpa using hunit 3 28 (by norm_num) (by norm_num)
  have hpositive {a b k : ℕ} (ha : 1 < a) (hm : a ≡ b [MOD 729])
      (hbmod : b % 3 = 2) (hbval : v3 (b + 1) = k) (hk : k < 6) :
      f3 a = (k : ℤ) := by
    have ha3 : a % 3 = 2 := by
      have h := hm.of_dvd (by norm_num : 3 ∣ 729)
      simpa only [Nat.ModEq, hbmod] using h
    have hplus : a + 1 ≡ b + 1 [MOD 3 ^ 6] := by
      simpa using hm.add_right 1
    have hv := v3_eq_of_modEq_pow_of_lt (by omega : a + 1 ≠ 0)
      (by omega : b + 1 ≠ 0) hplus (by omega : v3 (b + 1) < 6)
    rw [(f3_of_mod_three_two ha ha3).1, hv, hbval]
  have hnegative {a b k : ℕ} (ha : 1 < a) (hb : 1 < b)
      (hm : a ≡ b [MOD 729]) (hbmod : b % 3 = 1)
      (hbval : v3 (b - 1) = k) (hk : k < 6) : f3 a = -(k : ℤ) := by
    have ha3 : a % 3 = 1 := by
      have h := hm.of_dvd (by norm_num : 3 ∣ 729)
      simpa only [Nat.ModEq, hbmod] using h
    have hminus : a - 1 ≡ b - 1 [MOD 3 ^ 6] := by
      simpa using Nat.ModEq.sub_right (by omega : 1 ≤ a) (by omega : 1 ≤ b) hm
    have hv := v3_eq_of_modEq_pow_of_lt (by omega : a - 1 ≠ 0)
      (by omega : b - 1 ≠ 0) hminus (by omega : v3 (b - 1) < 6)
    rw [(f3_of_mod_three_one ha ha3).1, hv, hbval]
  obtain ⟨h0, h1, h2, h3⟩ := f3_pat1_point_mod729 hnmod hdmod
  obtain ⟨h01, h02, h03⟩ := f3_pat1_product_add_one_mod729 hnmod hdmod
  have hp1 : 1 < f3Pat1Point n d 1 := by
    change 1 < n + 38 * d
    omega
  have hp2 : 1 < f3Pat1Point n d 2 := by
    change 1 < n + 92 * d
    omega
  have hp3 : 1 < f3Pat1Point n d 3 := by
    change 1 < n + 146 * d
    omega
  have hp0 : 1 < f3Pat1Point n d 0 := hn
  have hm01 : f3Pat1Point n d 0 * f3Pat1Point n d 1 ≡ 215 [MOD 729] :=
    Nat.ModEq.add_right_cancel' 1 h01
  have hm02 : f3Pat1Point n d 0 * f3Pat1Point n d 2 ≡ 485 [MOD 729] :=
    Nat.ModEq.add_right_cancel' 1 h02
  have hm03 : f3Pat1Point n d 0 * f3Pat1Point n d 3 ≡ 755 [MOD 729] :=
    Nat.ModEq.add_right_cancel' 1 h03
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpositive hp0 h0 (by decide) hv6 (by decide)
  · exact hnegative hp1 (by decide) h1 (by decide) hv42 (by decide)
  · exact hnegative hp2 (by decide) h2 (by decide) hv96 (by decide)
  · exact hnegative hp3 (by decide) h3 (by decide) hv150 (by decide)
  · exact hpositive (by nlinarith : 1 < f3Pat1Point n d 0 * f3Pat1Point n d 1)
      hm01 (by decide) hv216 (by decide)
  · exact hpositive (by nlinarith : 1 < f3Pat1Point n d 0 * f3Pat1Point n d 2)
      hm02 (by decide) hv486 (by decide)
  · exact hpositive (by nlinarith : 1 < f3Pat1Point n d 0 * f3Pat1Point n d 3)
      hm03 (by decide) hv756 (by decide)

end OmegaBalance
