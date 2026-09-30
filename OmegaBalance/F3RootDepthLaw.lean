import OmegaBalance.F3RootDepthHaar

/-!
# Exact layers and unequal depths in the actual unit Haar model

This file continues REC-L3 from the genuine measure `f3UnitHaar` and genuine
extended root depths. The unequal-depth event is a disjoint union of two
level `L+1` balls. No probability formula is a hypothesis, and no subtraction
of infinite depths is performed. The full integer-valued signed-difference
law and its almost-everywhere treatment of root points remain separate work.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- A finite exact layer of the actual extended root depth. -/
def f3RootDepthLayer (a : ℤ_[3]) (t : ℕ) : Set ℤ_[3] :=
  {d | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = (t : WithTop ℤ)}

/-- An exact finite depth is the difference of two consecutive tails.
The infinite root point is removed automatically by this set difference. -/
theorem f3RootDepthLayer_eq_sdiff (a : ℤ_[3]) (t : ℕ) :
    f3RootDepthLayer a t = f3RootDepthTail a t \ f3RootDepthTail a (t + 1) := by
  ext d
  change rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = (t : WithTop ℤ) ↔
    (t : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ∧
      ¬((t + 1 : ℕ) : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (a : ℚ_[3])
  cases h : rootDepth (d : ℚ_[3]) (a : ℚ_[3]) using WithTop.recTopCoe with
  | top => simp
  | coe z => norm_cast <;> omega

/-- Every finite exact layer is measurable. -/
theorem f3RootDepthLayer_measurable (a : ℤ_[3]) (t : ℕ) :
    MeasurableSet (f3RootDepthLayer a t) := by
  rw [f3RootDepthLayer_eq_sdiff]
  exact (f3RootDepthTail_measurable a t).diff (f3RootDepthTail_measurable a (t + 1))

/-- The actual unit-root exact layer at positive depth has mass `3^(-t)`. -/
theorem f3UnitHaar_rootDepth_eq {a : ℤ_[3]} (ha : IsUnit a) {t : ℕ} (ht : 1 ≤ t) :
    f3UnitHaar (f3RootDepthLayer a t) = ((3 : ℝ≥0∞) ^ t)⁻¹ := by
  rw [f3RootDepthLayer_eq_sdiff,
    measure_sdiff (f3RootDepthTail_antitone a (Nat.le_succ t))
      (f3RootDepthTail_measurable a (t + 1)).nullMeasurableSet (measure_ne_top _ _),
    f3RootDepthTail_eq_fiber, f3UnitHaar_fiber ha ht,
    f3RootDepthTail_eq_fiber, f3UnitHaar_fiber ha (by omega), pow_succ,
    ENNReal.mul_inv (Or.inr (by norm_num : (3 : ℝ≥0∞) ≠ ⊤))
      (Or.inr (by norm_num : (3 : ℝ≥0∞) ≠ 0))]
  calc
    (2 / 3 : ℝ≥0∞)⁻¹ * (3 ^ t)⁻¹ -
        (2 / 3 : ℝ≥0∞)⁻¹ * ((3 ^ t)⁻¹ * 3⁻¹) =
      ((2 / 3 : ℝ≥0∞)⁻¹ - (2 / 3 : ℝ≥0∞)⁻¹ * 3⁻¹) * (3 ^ t)⁻¹ := by
        rw [ENNReal.sub_mul (by intro _ _; simp)]
        congr 1
        ac_rfl
    _ = (3 ^ t)⁻¹ := by
      have hc : (2 / 3 : ℝ≥0∞)⁻¹ - (2 / 3 : ℝ≥0∞)⁻¹ * 3⁻¹ = 1 := by
        simp only [ENNReal.inv_div (a := 2) (b := 3) (by norm_num) (by norm_num)]
        simp only [div_eq_mul_inv]
        have hp : (3 : ℝ≥0∞) * 2⁻¹ * 3⁻¹ = 2⁻¹ := by
          rw [mul_right_comm, ENNReal.mul_inv_cancel
            (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num : (3 : ℝ≥0∞) ≠ ⊤), one_mul]
        rw [hp]
        apply ENNReal.sub_eq_of_eq_add (by simp)
        calc
          (3 : ℝ≥0∞) * 2⁻¹ = (2 + 1) * 2⁻¹ := by norm_num
          _ = 2 * 2⁻¹ + 2⁻¹ := by rw [add_mul, one_mul]
          _ = 1 + 2⁻¹ := by
            rw [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      rw [hc, one_mul]

/-- At depth zero, the other unit residue class carries probability one half. -/
theorem f3UnitHaar_rootDepth_zero {a : ℤ_[3]} (ha : IsUnit a) :
    f3UnitHaar (f3RootDepthLayer a 0) = 1 / 2 := by
  have hcompl : (Set.univ \ f3RootDepthTail a (0 + 1)) =
      (f3RootDepthTail a 1)ᶜ := by
    ext d
    simp
  rw [f3RootDepthLayer_eq_sdiff, f3RootDepthTail_zero, hcompl,
    prob_compl_eq_one_sub (f3RootDepthTail_measurable a 1),
    f3UnitHaar_rootDepth_ge ha (by decide : 1 ≤ 1)]
  simpa only [Nat.sub_self, pow_zero, mul_one, one_div] using
    (ENNReal.sub_half (a := 1) (by norm_num))

/-- A threshold just above an integer is equivalent to a strict depth inequality. -/
theorem rootDepth_nat_lt_iff (d a : ℤ_[3]) (L : ℕ) :
    (L : WithTop ℤ) < rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ↔
      ((L + 1 : ℕ) : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (a : ℚ_[3]) := by
  cases h : rootDepth (d : ℚ_[3]) (a : ℚ_[3]) using WithTop.recTopCoe with
  | top => simp
  | coe z => norm_cast <;> omega

/-- REC-L3: unequal actual depths are exactly the two next-level root balls. -/
theorem rootDepth_ne_iff_mem_tail_union {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (d : ℤ_[3]) :
    rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3]) ↔
      d ∈ f3RootDepthTail a (L + 1) ∪ f3RootDepthTail b (L + 1) := by
  constructor
  · intro hne
    have hmin := rootDepth_min_eq_distance_of_ne hne
    rw [hL] at hmin
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      apply (rootDepth_nat_lt_iff d b L).mp
      rw [hmin, min_eq_left hlt.le]
      exact hlt
    · left
      apply (rootDepth_nat_lt_iff d a L).mp
      rw [hmin, min_eq_right hgt.le]
      exact hgt
  · intro hd heq
    have hmin := rootDepth_min_le_distance (d : ℚ_[3]) (a : ℚ_[3]) (b : ℚ_[3])
    rw [hL, heq, min_self] at hmin
    rcases hd with ha | hb
    · have hlt := (rootDepth_nat_lt_iff d a L).mpr ha
      rw [heq] at hlt
      exact (not_lt_of_ge hmin) hlt
    · exact (not_lt_of_ge hmin) ((rootDepth_nat_lt_iff d b L).mpr hb)

/-- The two next-level balls are disjoint when the actual root distance is `L`. -/
theorem f3RootDepthTail_disjoint {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    Disjoint (f3RootDepthTail a (L + 1)) (f3RootDepthTail b (L + 1)) := by
  refine Set.disjoint_left.mpr ?_
  intro d ha hb
  have hmin := rootDepth_min_le_distance (d : ℚ_[3]) (a : ℚ_[3]) (b : ℚ_[3])
  rw [hL] at hmin
  have hlt : (L : WithTop ℤ) <
      min (rootDepth (d : ℚ_[3]) (a : ℚ_[3]))
        (rootDepth (d : ℚ_[3]) (b : ℚ_[3])) :=
    lt_min ((rootDepth_nat_lt_iff d a L).mpr ha) ((rootDepth_nat_lt_iff d b L).mpr hb)
  exact (not_lt_of_ge hmin) hlt

/-- REC-L3 single-observation certificate probability for actual unit roots.
The finite-distance hypothesis itself excludes equal roots; `L≥1` retains
the paper's common first residue class. -/
theorem f3UnitHaar_rootDepth_ne {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (_hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnitHaar {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])} =
        ((3 : ℝ≥0∞) ^ L)⁻¹ := by
  have hevent : {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])} =
      f3RootDepthTail a (L + 1) ∪ f3RootDepthTail b (L + 1) := by
    ext d
    exact rootDepth_ne_iff_mem_tail_union hL d
  rw [hevent, measure_union (f3RootDepthTail_disjoint hL)
    (f3RootDepthTail_measurable b (L + 1)),
    f3UnitHaar_rootDepth_ge ha (by omega), f3UnitHaar_rootDepth_ge hb (by omega)]
  simp only [Nat.add_sub_cancel]
  simp only [ENNReal.mul_inv (a := 2) (b := (3 : ℝ≥0∞) ^ L)
    (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
  rw [← add_mul]
  have hhalf : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
    simpa only [one_div] using (ENNReal.add_halves (1 : ℝ≥0∞))
  rw [hhalf, one_mul]

end

end OmegaBalance
