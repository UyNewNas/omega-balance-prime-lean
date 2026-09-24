import OmegaBalance.F3Extension

/-!
# F₃ multiplication, differences and reflection

`f3Side` records the sign for n > 1 with 3 ∤ n. All valuation subtraction is
performed in ℤ, so an adjusted gap is never silently truncated to zero.
Zero hypotheses on valuation arguments are essential: v₃(0) is totalized.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Residue-defined side of the divisible neighbor; equals sign(F₃) on its ordinary domain. -/
def f3Side (n : ℕ) : ℤ := if n % 3 = 2 then 1 else -1

theorem f3Side_values (n : ℕ) : f3Side n = 1 ∨ f3Side n = -1 := by
  unfold f3Side
  split_ifs <;> simp

theorem f3_eq_side_mul_natAbs {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 n = f3Side n * ((f3 n).natAbs : ℤ) := by
  have hm : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with h | h
  · rw [(f3_of_mod_three_one hn h).1]
    simp [f3Side, h]
  · rw [(f3_of_mod_three_two hn h).1]
    simp [f3Side, h]

theorem f3_center_pos {n : ℕ} (hn : 1 < n) : 0 < (n : ℤ) + f3Side n := by
  rcases f3Side_values n with h | h <;> omega

/-- The center on the divisible side has exactly the depth recorded by F₃. -/
theorem f3_center_valuation {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    v3Int ((n : ℤ) + f3Side n) = (f3 n).natAbs := by
  have hm : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with h | h
  · have he : (n : ℤ) + (-1) = ((n - 1 : ℕ) : ℤ) := by omega
    rw [(f3_of_mod_three_one hn h).1]
    simp [f3Side, h, he]
  · have he : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by simp
    rw [(f3_of_mod_three_two hn h).1]
    simp [f3Side, h, he]

/-- Bridge to the rational valuation API used for its ultrametric laws. -/
theorem v3Int_eq_padicValRat (z : ℤ) :
    (v3Int z : ℤ) = padicValRat 3 (z : ℚ) := by
  simp [v3Int]

theorem v3Int_add_ge_min {a b : ℤ} (hab : a + b ≠ 0) :
    min (v3Int a) (v3Int b) ≤ v3Int (a + b) := by
  have h := padicValRat.min_le_padicValRat_add (p := 3)
    (q := (a : ℚ)) (r := (b : ℚ)) (by exact_mod_cast hab)
  simp only [← Int.cast_add, ← v3Int_eq_padicValRat] at h
  exact_mod_cast h

theorem v3Int_add_eq_min {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) (hv : v3Int a ≠ v3Int b) :
    v3Int (a + b) = min (v3Int a) (v3Int b) := by
  have hv' : padicValRat 3 (a : ℚ) ≠ padicValRat 3 (b : ℚ) := by
    simpa only [← v3Int_eq_padicValRat, Nat.cast_inj] using hv
  have h := padicValRat.add_eq_min (p := 3) (q := (a : ℚ)) (r := (b : ℚ))
    (by exact_mod_cast hab) (by exact_mod_cast ha) (by exact_mod_cast hb) hv'
  simp only [← Int.cast_add, ← v3Int_eq_padicValRat] at h
  exact_mod_cast h

theorem v3Int_sub_eq_min {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hv : v3Int a ≠ v3Int b) :
    v3Int (a - b) = min (v3Int a) (v3Int b) := by
  have hh : a + -b ≠ 0 := by omega
  simpa only [sub_eq_add_neg, v3Int_neg] using
    v3Int_add_eq_min ha (neg_ne_zero.mpr hb) hh (by simpa using hv)

/-- The unequal-depth gap law works for arbitrary 3-coprime integers > 1. -/
theorem f3_adjusted_gap_valuation {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hp3 : ¬ 3 ∣ p) (hq3 : ¬ 3 ∣ q) (hd : (f3 p).natAbs ≠ (f3 q).natAbs) :
    v3Int ((q : ℤ) - p + f3Side q - f3Side p) =
      min (f3 q).natAbs (f3 p).natAbs := by
  have hne : (q : ℤ) + f3Side q ≠ (p : ℤ) + f3Side p := by
    intro h
    have hv := congrArg v3Int h
    rw [f3_center_valuation hq hq3, f3_center_valuation hp hp3] at hv
    exact hd hv.symm
  have hv : v3Int ((q : ℤ) + f3Side q) ≠ v3Int ((p : ℤ) + f3Side p) := by
    rw [f3_center_valuation hq hq3, f3_center_valuation hp hp3]
    exact Ne.symm hd
  have he : (q : ℤ) - p + f3Side q - f3Side p =
      ((q : ℤ) + f3Side q) - ((p : ℤ) + f3Side p) := by ring
  rw [he, v3Int_sub_eq_min (ne_of_gt (f3_center_pos hq))
    (ne_of_gt (f3_center_pos hp)) hne hv,
    f3_center_valuation hq hq3, f3_center_valuation hp hp3]

/-- A fixed-sum reflection locks a lower depth to its exact opposite.
Primality and evenness of the total are both unnecessary. -/
theorem f3_reflection {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (ha3 : ¬ 3 ∣ a) (hs : 3 ∣ a + b) (hd : (f3 a).natAbs < v3 (a + b)) :
    f3 b = -f3 a := by
  have hsmod := Nat.mod_eq_zero_of_dvd hs
  have hamod : a % 3 ≠ 0 := fun h => ha3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hbmod : b % 3 ≠ 0 := by omega
  have hb3 : ¬ 3 ∣ b := fun h => hbmod (Nat.mod_eq_zero_of_dvd h)
  have hside : f3Side b = -f3Side a := by
    have cases : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases cases with h | h
    · have hh : b % 3 = 2 := by omega
      simp [f3Side, h, hh]
    · have hh : b % 3 = 1 := by omega
      simp [f3Side, h, hh]
  have hrel : ((a + b : ℕ) : ℤ) - ((a : ℤ) + f3Side a) =
      (b : ℤ) + f3Side b := by
    rw [hside]
    push_cast
    ring
  have hne : ((a + b : ℕ) : ℤ) ≠ (a : ℤ) + f3Side a := by
    have hpos := f3_center_pos hb
    intro h
    rw [h, sub_self] at hrel
    omega
  have hv : v3Int ((a + b : ℕ) : ℤ) ≠ v3Int ((a : ℤ) + f3Side a) := by
    rw [v3Int_nat, f3_center_valuation ha ha3]
    omega
  have he := v3Int_sub_eq_min (a := ((a + b : ℕ) : ℤ))
    (b := (a : ℤ) + f3Side a) (by omega) (ne_of_gt (f3_center_pos ha)) hne hv
  rw [hrel, f3_center_valuation hb hb3, v3Int_nat,
    f3_center_valuation ha ha3, min_eq_right (Nat.le_of_lt hd)] at he
  rw [f3_eq_side_mul_natAbs hb hb3, f3_eq_side_mul_natAbs ha ha3, he, hside]
  ring

/-- Signs obey a simple multiplicative rule; no prime hypothesis is used. -/
theorem f3Side_mul {m n : ℕ} (hm : ¬ 3 ∣ m) (hn : ¬ 3 ∣ n) :
    f3Side (m * n) = -f3Side m * f3Side n := by
  have hmr : m % 3 ≠ 0 := fun h => hm (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hnr : n % 3 ≠ 0 := fun h => hn (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hc : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hd : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hc with h | h <;> rcases hd with h' | h' <;>
    norm_num [f3Side, Nat.mul_mod, h, h']

/-- Repeated cubing of a positive-side integer adds one depth at each step. -/
theorem f3_iterated_cube_pos {n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) (r : ℕ) :
    (n ^ (3 ^ r)) % 3 = 2 ∧ f3 (n ^ (3 ^ r)) = f3 n + (r : ℤ) := by
  induction r with
  | zero => simpa using And.intro hm (show f3 n = f3 n by rfl)
  | succ r ih =>
    have hpow : n ^ (3 ^ (r + 1)) = (n ^ (3 ^ r)) ^ 3 := by rw [pow_succ, pow_mul]
    have hn' : 1 < n ^ (3 ^ r) := Nat.one_lt_pow (pow_ne_zero r (by decide)) hn
    rw [hpow]
    constructor
    · norm_num [Nat.pow_mod, ih.1]
    · rw [f3_cube_of_mod_three_two hn' ih.1, ih.2]
      push_cast
      ring

/-- Repeated cubing of a negative-side integer subtracts one at each step. -/
theorem f3_iterated_cube_neg {n : ℕ} (hn : 1 < n) (hm : n % 3 = 1) (r : ℕ) :
    (n ^ (3 ^ r)) % 3 = 1 ∧ f3 (n ^ (3 ^ r)) = f3 n - (r : ℤ) := by
  induction r with
  | zero => simpa using And.intro hm (show f3 n = f3 n by rfl)
  | succ r ih =>
    have hpow : n ^ (3 ^ (r + 1)) = (n ^ (3 ^ r)) ^ 3 := by rw [pow_succ, pow_mul]
    have hn' : 1 < n ^ (3 ^ r) := Nat.one_lt_pow (pow_ne_zero r (by decide)) hn
    rw [hpow]
    constructor
    · norm_num [Nat.pow_mod, ih.1]
    · rw [f3_cube_of_mod_three_one hn' ih.1, ih.2]
      push_cast
      ring

/-- Natural-number form of the ultrametric lower bound. -/
theorem v3_add_ge_min {a b : ℕ} (hab : a + b ≠ 0) :
    min (v3 a) (v3 b) ≤ v3 (a + b) := by
  have h := v3Int_add_ge_min (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast hab)
  simpa only [← Nat.cast_add, v3Int_nat] using h

theorem v3_add_eq_min {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : v3 a ≠ v3 b) : v3 (a + b) = min (v3 a) (v3 b) := by
  have h := v3Int_add_eq_min (a := (a : ℤ)) (b := (b : ℤ))
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by omega)
    (by simpa only [v3Int_nat] using hv)
  simpa only [← Nat.cast_add, v3Int_nat] using h

/-- Multiplication cannot lower depth below the smaller input depth;
when the depths differ, the lower bound is exact. -/
theorem f3_mul_depth {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    min |f3 m| |f3 n| ≤ |f3 (m * n)| ∧
      (|f3 m| ≠ |f3 n| → |f3 (m * n)| = min |f3 m| |f3 n|) := by
  have hmn : 1 < m * n := by nlinarith
  have hmn3 : ¬ 3 ∣ m * n := by
    intro h
    rcases Nat.prime_three.dvd_mul.mp h with h | h
    · exact hm3 h
    · exact hn3 h
  have hnr : n % 3 ≠ 0 := fun h => hn3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hsqmod : n ^ 2 % 3 = 1 := by
    rcases cases with h | h <;> norm_num [Nat.pow_mod, h]
  have hz : v3 (n ^ 2) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro h
    have hh := Nat.mod_eq_zero_of_dvd h
    omega
  have hx : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hy : n ^ 2 - 1 ≠ 0 := by nlinarith
  have hn2 : n ^ 2 ≠ 0 := by nlinarith
  have hmul : v3 ((m ^ 2 - 1) * n ^ 2) = v3 (m ^ 2 - 1) := by
    rw [v3_mul hx hn2, hz, add_zero]
  have h1 : m ^ 2 - 1 + 1 = m ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have h2 : n ^ 2 - 1 + 1 = n ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have h3 : (m * n) ^ 2 - 1 + 1 = (m * n) ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hh := congrArg (fun x : ℕ => x * n ^ 2) h1
  have hid : (m ^ 2 - 1) * n ^ 2 + (n ^ 2 - 1) = (m * n) ^ 2 - 1 := by
    nlinarith [hh]
  rw [f3_abs_eq_v3_sq_sub_one hm hm3, f3_abs_eq_v3_sq_sub_one hn hn3,
    f3_abs_eq_v3_sq_sub_one hmn hmn3]
  constructor
  · have he := v3_add_ge_min (a := (m ^ 2 - 1) * n ^ 2)
      (b := n ^ 2 - 1) (by omega)
    rw [hmul, hid] at he
    exact_mod_cast he
  · intro hd
    have hv : v3 ((m ^ 2 - 1) * n ^ 2) ≠ v3 (n ^ 2 - 1) := by
      rw [hmul]
      exact_mod_cast hd
    have he := v3_add_eq_min (mul_ne_zero hx hn2) hy hv
    rw [hmul, hid] at he
    exact_mod_cast he

end OmegaBalance
