import OmegaBalance.F3ConditionalDepthLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Full conditional independence of actual sign and absolute difference

The integer-valued representative below is explicitly arbitrary at root hits:
`untopD 0` is used only for total measurability. The genuine root depth remains
infinite there. Before transferring any law, we prove equivalence with genuine
finite signed atoms almost everywhere under the actual conditional measure.
The final target is `IndepFun`, obtained from equality of whole pushforward
measures, not merely a single factorized probability.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- A measurable representative; its values at the two null root points are arbitrary. -/
def f3SignedDepthValue (a b : ℤ_[3]) (d : ℤ_[3]) : ℤ :=
  (f3RootDepthObservation a d).untopD 0 - (f3RootDepthObservation b d).untopD 0

/-- Away from infinite depth, the representative is the genuine integer difference. -/
theorem f3SignedDepthValue_eq_of_depths {a b d : ℤ_[3]} {r s : ℤ}
    (hr : rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = (r : WithTop ℤ))
    (hs : rootDepth (d : ℚ_[3]) (b : ℚ_[3]) = (s : WithTop ℤ)) :
    f3SignedDepthValue a b d = r - s := by
  unfold f3SignedDepthValue f3RootDepthObservation
  rw [hr, hs]
  rfl

/-- Total measurability uses the standard Borel untop map, not a custom measurable space. -/
theorem f3SignedDepthValue_measurable (a b : ℤ_[3]) : Measurable (f3SignedDepthValue a b) :=
  ((f3RootDepthObservation_measurable a).untopD 0).sub
    ((f3RootDepthObservation_measurable b).untopD 0)

/-- Every atom of the representative equals the genuine finite atom almost everywhere. -/
theorem f3SignedDepthValue_event_ae (a b : ℤ_[3]) (h : ℤ) :
    {d : ℤ_[3] | f3SignedDepthValue a b d = h} =ᵐ[f3UnequalDepthHaar a b]
      f3SignedDepthEvent a b h := by
  filter_upwards [f3UnequalDepthHaar_signedDepth_defined_ae a b] with d hd
  rcases hd with ⟨k, r, s, hr, hs, _⟩
  apply propext
  change f3SignedDepthValue a b d = h ↔ ∃ u v : ℤ,
    rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = (u : WithTop ℤ) ∧
    rootDepth (d : ℚ_[3]) (b : ℚ_[3]) = (v : WithTop ℤ) ∧ u - v = h
  rw [f3SignedDepthValue_eq_of_depths hr hs]
  constructor
  · intro hh
    exact ⟨r, s, hr, hs, hh⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    have hru : r = u := by exact_mod_cast (hr.symm.trans hu)
    have hsv : s = v := by exact_mod_cast (hs.symm.trans hv)
    omega

/-- Actual sign of the measurable signed-difference representative. -/
def f3DepthSign (a b : ℤ_[3]) (d : ℤ_[3]) : Bool := decide (0 < f3SignedDepthValue a b d)

/-- Actual absolute size of the same signed-difference representative. -/
def f3DepthSize (a b : ℤ_[3]) (d : ℤ_[3]) : ℕ := (f3SignedDepthValue a b d).natAbs

/-- The sign observable is measurable. -/
theorem f3DepthSign_measurable (a b : ℤ_[3]) : Measurable (f3DepthSign a b) :=
  (measurable_of_countable (fun z : ℤ => decide (0 < z))).comp
    (f3SignedDepthValue_measurable a b)

/-- The absolute-size observable is measurable. -/
theorem f3DepthSize_measurable (a b : ℤ_[3]) : Measurable (f3DepthSize a b) :=
  (measurable_of_countable Int.natAbs).comp (f3SignedDepthValue_measurable a b)

/-- Strict orientation is one genuine next-level root ball, including its infinite root point. -/
theorem rootDepth_lt_iff_mem_first_tail {a b : ℤ_[3]} {L : ℕ}
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (d : ℤ_[3]) :
    rootDepth (d : ℚ_[3]) (b : ℚ_[3]) < rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ↔
      d ∈ f3RootDepthTail a (L + 1) := by
  constructor
  · intro hgt
    have hm := rootDepth_min_eq_distance_of_ne (ne_of_gt hgt)
    rw [hL, min_eq_right hgt.le] at hm
    apply (rootDepth_nat_lt_iff d a L).mp
    rw [hm]
    exact hgt
  · intro hd
    have hgt := (rootDepth_nat_lt_iff d a L).mpr hd
    rw [← hL] at hgt
    rw [rootDepth_eq_distance_of_lt hgt]
    exact hgt

/-- The representative sign agrees almost everywhere with strict extended-depth orientation. -/
theorem f3DepthSign_true_event_ae (a b : ℤ_[3]) :
    {d : ℤ_[3] | f3DepthSign a b d = true} =ᵐ[f3UnequalDepthHaar a b]
      {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (b : ℚ_[3]) <
        rootDepth (d : ℚ_[3]) (a : ℚ_[3])} := by
  filter_upwards [f3UnequalDepthHaar_signedDepth_defined_ae a b] with d hd
  rcases hd with ⟨k, r, s, hr, hs, _⟩
  apply propext
  change decide (0 < f3SignedDepthValue a b d) = true ↔
    rootDepth (d : ℚ_[3]) (b : ℚ_[3]) < rootDepth (d : ℚ_[3]) (a : ℚ_[3])
  rw [f3SignedDepthValue_eq_of_depths hr hs, hr, hs]
  simp only [decide_eq_true_eq, WithTop.coe_lt_coe]
  omega

/-- Fair positive sign under the genuine conditional measure. -/
theorem f3UnequalDepthHaar_sign_true {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    f3UnequalDepthHaar a b {d | f3DepthSign a b d = true} = 1 / 2 := by
  rw [measure_congr (f3DepthSign_true_event_ae a b)]
  have he : {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (b : ℚ_[3]) <
      rootDepth (d : ℚ_[3]) (a : ℚ_[3])} = f3RootDepthTail a (L + 1) := by
    ext d
    exact rootDepth_lt_iff_mem_first_tail hL d
  have hsub : f3RootDepthTail a (L + 1) ⊆ {d : ℤ_[3] |
      rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ≠ rootDepth (d : ℚ_[3]) (b : ℚ_[3])} := by
    intro d hd
    exact ne_of_gt ((rootDepth_lt_iff_mem_first_tail hL d).mpr hd)
  rw [he, f3UnequalDepthHaar, cond_apply (f3RootDepth_ne_measurable hL),
    Set.inter_eq_right.mpr hsub, f3UnitHaar_rootDepth_ne ha hb hLpos hL,
    f3UnitHaar_rootDepth_ge ha (by omega), Nat.add_sub_cancel, inv_inv]
  have h0 : (3 : ℝ≥0∞) ^ L ≠ 0 := by simp
  have ht : (3 : ℝ≥0∞) ^ L ≠ ⊤ := by simp
  rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)), mul_left_comm,
    ENNReal.mul_inv_cancel h0 ht, mul_one, one_div]

/-- Both Boolean sign values have probability one half. -/
theorem f3UnequalDepthHaar_sign_eq {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (v : Bool) :
    f3UnequalDepthHaar a b {d | f3DepthSign a b d = v} = 1 / 2 := by
  letI := f3UnequalDepthHaar_isProbability ha hb hLpos hL
  cases v with
  | true => exact f3UnequalDepthHaar_sign_true ha hb hLpos hL
  | false =>
    have he : {d : ℤ_[3] | f3DepthSign a b d = false} =
        {d : ℤ_[3] | f3DepthSign a b d = true}ᶜ := by
      ext d
      cases f3DepthSign a b d <;> simp
    have hm : MeasurableSet {d : ℤ_[3] | f3DepthSign a b d = true} :=
      (f3DepthSign_measurable a b) (measurableSet_singleton true)
    rw [he, prob_compl_eq_one_sub hm, f3UnequalDepthHaar_sign_true ha hb hLpos hL]
    exact ENNReal.sub_half (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)

/-- Absolute size agrees almost everywhere with the genuine finite absolute event. -/
theorem f3DepthSize_event_ae (a b : ℤ_[3]) (n : ℕ) :
    {d : ℤ_[3] | f3DepthSize a b d = n} =ᵐ[f3UnequalDepthHaar a b]
      f3AbsDepthEvent a b n := by
  filter_upwards [f3UnequalDepthHaar_signedDepth_defined_ae a b] with d hd
  rcases hd with ⟨k, r, s, hr, hs, _⟩
  apply propext
  change (f3SignedDepthValue a b d).natAbs = n ↔ d ∈ f3AbsDepthEvent a b n
  rw [f3SignedDepthValue_eq_of_depths hr hs, f3AbsDepthEvent_iff]
  constructor
  · intro hn
    exact ⟨r, s, hr, hs, hn⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    have hru : r = u := by exact_mod_cast (hr.symm.trans hu)
    have hsv : s = v := by exact_mod_cast (hs.symm.trans hv)
    simpa only [hru, hsv] using huv

/-- The entire absolute-size marginal, including zero, comes from actual conditional observations. -/
theorem f3UnequalDepthHaar_size_eq {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (n : ℕ) :
    f3UnequalDepthHaar a b {d | f3DepthSize a b d = n} =
      if n = 0 then 0 else 2 * ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [measure_congr (f3DepthSize_event_ae a b n)]
  by_cases hn : n = 0
  · subst n
    simp only [f3AbsDepthEvent, Nat.cast_zero, neg_zero, Set.union_self, if_pos rfl]
    exact f3UnequalDepthHaar_signed_zero hL
  · rw [if_neg hn]
    exact f3UnequalDepthHaar_abs_eq ha hb hLpos (by omega) hL

/-- A positive-size joint atom specifies exactly one actual signed integer value. -/
theorem f3DepthSign_size_atom {a b : ℤ_[3]} (v : Bool) {n : ℕ} (hn : 1 ≤ n) :
    {d : ℤ_[3] | (f3DepthSign a b d, f3DepthSize a b d) = (v, n)} =
      {d : ℤ_[3] | f3SignedDepthValue a b d = if v then (n : ℤ) else -(n : ℤ)} := by
  ext d
  cases v <;> by_cases hz : 0 < f3SignedDepthValue a b d <;>
    simp [f3DepthSign, f3DepthSize, hz, Int.natAbs_eq_iff] <;> omega

/-- The complete actual joint atomic law; the zero-size exceptional case has mass zero. -/
theorem f3UnequalDepthHaar_sign_size_eq {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) (v : Bool) (n : ℕ) :
    f3UnequalDepthHaar a b {d | (f3DepthSign a b d, f3DepthSize a b d) = (v, n)} =
      if n = 0 then 0 else ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl]
    apply le_antisymm _ zero_le
    have hs : {d : ℤ_[3] | (f3DepthSign a b d, f3DepthSize a b d) = (v, 0)} ⊆
        {d : ℤ_[3] | f3DepthSize a b d = 0} := by
      intro d hd
      exact congrArg Prod.snd hd
    exact (measure_mono hs).trans_eq (by simpa using f3UnequalDepthHaar_size_eq ha hb hLpos hL 0)
  · rw [if_neg hn, f3DepthSign_size_atom v (by omega)]
    cases v with
    | true =>
      change f3UnequalDepthHaar a b {d | f3SignedDepthValue a b d = (n : ℤ)} =
        ((3 : ℝ≥0∞) ^ n)⁻¹
      rw [measure_congr (f3SignedDepthValue_event_ae a b (n : ℤ))]
      exact f3UnequalDepthHaar_signed_pos ha hb hLpos (by omega) hL
    | false =>
      change f3UnequalDepthHaar a b {d | f3SignedDepthValue a b d = -(n : ℤ)} =
        ((3 : ℝ≥0∞) ^ n)⁻¹
      rw [measure_congr (f3SignedDepthValue_event_ae a b (-(n : ℤ)))]
      exact f3UnequalDepthHaar_signed_neg ha hb hLpos (by omega) hL

/-- Full independence follows from equality of actual joint and product pushforward measures. -/
theorem f3UnequalDepthHaar_sign_size_indep {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    {L : ℕ} (hLpos : 1 ≤ L)
    (hL : rootDistance (a : ℚ_[3]) (b : ℚ_[3]) = (L : WithTop ℤ)) :
    IndepFun (f3DepthSign a b) (f3DepthSize a b) (f3UnequalDepthHaar a b) := by
  letI := f3UnequalDepthHaar_isProbability ha hb hLpos hL
  have hsign := f3DepthSign_measurable a b
  have hsize := f3DepthSize_measurable a b
  apply (indepFun_iff_map_prod_eq_prod_map_map hsign.aemeasurable hsize.aemeasurable).mpr
  apply Measure.ext_of_singleton
  rintro ⟨v, n⟩
  have hp : ((f3UnequalDepthHaar a b).map (f3DepthSign a b)).prod
      ((f3UnequalDepthHaar a b).map (f3DepthSize a b)) {(v, n)} =
      (f3UnequalDepthHaar a b).map (f3DepthSign a b) {v} *
        (f3UnequalDepthHaar a b).map (f3DepthSize a b) {n} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [hp, Measure.map_apply (hsign.prodMk hsize) (measurableSet_singleton (v, n)),
    Measure.map_apply hsign (measurableSet_singleton v),
    Measure.map_apply hsize (measurableSet_singleton n)]
  change f3UnequalDepthHaar a b {d | (f3DepthSign a b d, f3DepthSize a b d) = (v, n)} =
    f3UnequalDepthHaar a b {d | f3DepthSign a b d = v} *
      f3UnequalDepthHaar a b {d | f3DepthSize a b d = n}
  rw [f3UnequalDepthHaar_sign_size_eq ha hb hLpos hL,
    f3UnequalDepthHaar_sign_eq ha hb hLpos hL, f3UnequalDepthHaar_size_eq ha hb hLpos hL]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn, one_div]
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]

/-- Full sign/absolute-size independence on the unchanged original shared-root model. -/
theorem f3SharedRootConfig_conditional_sign_size_indep {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L : ℕ}
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    IndepFun (f3DepthSign (f3SharedRootUnit C i) (f3SharedRootUnit C j))
      (f3DepthSize (f3SharedRootUnit C i) (f3SharedRootUnit C j))
      (f3UnequalDepthHaar (f3SharedRootUnit C i) (f3SharedRootUnit C j)) := by
  have hpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  apply f3UnequalDepthHaar_sign_size_indep (f3SharedRootUnit_isUnit C i)
    (f3SharedRootUnit_isUnit C j) hpos
  simpa only [f3SharedRootUnit_coe] using hL

end

end OmegaBalance
