import OmegaBalance.F3TruncatedBatchHaar
import OmegaBalance.F3RootDepthNull
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Map

/-!
# Actual finite-precision observation laws and nonidentifiability

The observable is the existing extended root depth, not a stipulated PMF or a
zero-totalized valuation. Its standard WithTop-Int Borel measurability is proved
from actual tails and the root singleton. Exact tail masses identify the whole
pushforward law. Truncation and the diagonal then give the full two-output law
when both root distances are at least H, and the existing product-map theorem
gives equality for every finite batch of independent complete observations.

This concerns information in local Haar observations alone, not separately
supplied coefficients or equality of finite prime-box sampling laws.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory Set

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The actual raw extended-depth observable on three-adic integer samples. -/
def f3RootDepthObservation (a : ℤ_[3]) (d : ℤ_[3]) : WithTop ℤ :=
  rootDepth (d : ℚ_[3]) (a : ℚ_[3])

/-- Integer samples and roots have nonnegative actual depth, including infinity. -/
theorem f3RootDepthObservation_nonneg (a d : ℤ_[3]) :
    (0 : WithTop ℤ) ≤ f3RootDepthObservation a d := by
  change d ∈ f3RootDepthTail a 0
  rw [f3RootDepthTail_zero]
  exact Set.mem_univ d

/-- The top half-line pulls back to the genuine root singleton. -/
theorem f3RootDepthObservation_preimage_top (a : ℤ_[3]) :
    f3RootDepthObservation a ⁻¹' Ici ⊤ = {a} := by
  ext d
  change (⊤ : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ↔ d = a
  rw [top_le_iff, rootDepth_eq_top_iff]
  exact ⟨PadicInt.ext, fun h => congrArg (fun x : ℤ_[3] => (x : ℚ_[3])) h⟩

/-- Nonpositive integer thresholds are attained by every actual sample. -/
theorem f3RootDepthObservation_preimage_nonpos (a : ℤ_[3]) {z : ℤ} (hz : z ≤ 0) :
    f3RootDepthObservation a ⁻¹' Ici (z : WithTop ℤ) = Set.univ := by
  ext d
  simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
  have hz' : (z : WithTop ℤ) ≤ 0 := by exact_mod_cast hz
  exact hz'.trans (f3RootDepthObservation_nonneg a d)

/-- Natural-threshold preimages are exactly the already proved genuine residue tails. -/
theorem f3RootDepthObservation_preimage_nat (a : ℤ_[3]) (n : ℕ) :
    f3RootDepthObservation a ⁻¹' Ici (n : WithTop ℤ) = f3RootDepthTail a n := rfl

/-- The entire extended observable is measurable, including its infinite root value. -/
theorem f3RootDepthObservation_measurable (a : ℤ_[3]) :
    Measurable (f3RootDepthObservation a) := by
  apply measurable_of_Ici
  intro k
  cases k using WithTop.recTopCoe with
  | top =>
    rw [f3RootDepthObservation_preimage_top]
    exact measurableSet_singleton a
  | coe z =>
    by_cases hz : z ≤ 0
    · rw [f3RootDepthObservation_preimage_nonpos a hz]
      exact MeasurableSet.univ
    · have hcast : (z.toNat : WithTop ℤ) = (z : WithTop ℤ) :=
        congrArg (fun x : ℤ => (x : WithTop ℤ))
          (Int.toNat_of_nonneg (lt_of_not_ge hz).le)
      rw [← hcast, f3RootDepthObservation_preimage_nat]
      exact f3RootDepthTail_measurable a z.toNat

/-- Existing actual tail masses determine the whole unit-root depth distribution. -/
theorem f3UnitHaar_rootDepth_map_eq {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b) :
    f3UnitHaar.map (f3RootDepthObservation a) =
      f3UnitHaar.map (f3RootDepthObservation b) := by
  apply Measure.ext_of_Ici
  intro k
  rw [Measure.map_apply (f3RootDepthObservation_measurable a) measurableSet_Ici,
    Measure.map_apply (f3RootDepthObservation_measurable b) measurableSet_Ici]
  cases k using WithTop.recTopCoe with
  | top =>
    rw [f3RootDepthObservation_preimage_top, f3RootDepthObservation_preimage_top,
      f3UnitHaar_singleton, f3UnitHaar_singleton]
  | coe z =>
    by_cases hz : z ≤ 0
    · rw [f3RootDepthObservation_preimage_nonpos a hz,
        f3RootDepthObservation_preimage_nonpos b hz]
    · have hcast : (z.toNat : WithTop ℤ) = (z : WithTop ℤ) :=
        congrArg (fun x : ℤ => (x : WithTop ℤ))
          (Int.toNat_of_nonneg (lt_of_not_ge hz).le)
      have hn : 1 ≤ z.toNat := by omega
      rw [← hcast, f3RootDepthObservation_preimage_nat,
        f3RootDepthObservation_preimage_nat,
        f3UnitHaar_rootDepth_ge ha hn, f3UnitHaar_rootDepth_ge hb hn]

/-- The finite-precision observation is the existing normalized cutoff of actual depth. -/
def f3TruncatedDepthObservation (a : ℤ_[3]) (H : ℕ) (d : ℤ_[3]) : WithTop ℤ :=
  truncatedRootDepth H (d : ℚ_[3]) (a : ℚ_[3])

/-- Truncation is a measurable map of the genuine extended observation. -/
theorem f3TruncatedDepthObservation_measurable (a : ℤ_[3]) (H : ℕ) :
    Measurable (f3TruncatedDepthObservation a H) :=
  (f3RootDepthObservation_measurable a).min measurable_const

/-- The entire truncated marginal law is independent of the particular unit root. -/
theorem f3UnitHaar_truncatedDepth_map_eq {a b : ℤ_[3]} (ha : IsUnit a) (hb : IsUnit b)
    (H : ℕ) :
    f3UnitHaar.map (f3TruncatedDepthObservation a H) =
      f3UnitHaar.map (f3TruncatedDepthObservation b H) := by
  have hc : Measurable (fun z : WithTop ℤ => min z (H : WithTop ℤ)) :=
    measurable_id.min measurable_const
  change f3UnitHaar.map ((fun z : WithTop ℤ => min z (H : WithTop ℤ)) ∘
      f3RootDepthObservation a) =
    f3UnitHaar.map ((fun z : WithTop ℤ => min z (H : WithTop ℤ)) ∘
      f3RootDepthObservation b)
  rw [← Measure.map_map hc (f3RootDepthObservation_measurable a),
    ← Measure.map_map hc (f3RootDepthObservation_measurable b),
    f3UnitHaar_rootDepth_map_eq ha hb]

/-- Roots in the same H-ball yield identical truncated coordinates on every sample. -/
theorem truncatedRootDepth_eq_of_le_distance {H : ℕ} {d a b : ℚ_[3]}
    (hL : (H : WithTop ℤ) ≤ rootDistance a b) :
    truncatedRootDepth H d a = truncatedRootDepth H d b := by
  by_contra hne
  have h := truncatedRootDepth_ne_certificate hne
  exact (not_lt_of_ge hL) (h.1.trans_lt h.2)

/-- The actual ordered two-coordinate observation from a shared sample parameter. -/
def f3TruncatedPairObservation (a b : ℤ_[3]) (H : ℕ) (d : ℤ_[3]) :
    WithTop ℤ × WithTop ℤ :=
  (f3TruncatedDepthObservation a H d, f3TruncatedDepthObservation b H d)

/-- Both coordinates use the same sample and form a measurable observation. -/
theorem f3TruncatedPairObservation_measurable (a b : ℤ_[3]) (H : ℕ) :
    Measurable (f3TruncatedPairObservation a b H) :=
  (f3TruncatedDepthObservation_measurable a H).prodMk
    (f3TruncatedDepthObservation_measurable b H)

/-- Complete two-output law equality above precision, not merely a moment identity. -/
theorem f3UnitHaar_truncatedPair_map_eq {a b a' b' : ℤ_[3]}
    (ha : IsUnit a) (_hb : IsUnit b) (ha' : IsUnit a') (_hb' : IsUnit b')
    {H : ℕ} (_hH : 1 ≤ H)
    (hL : (H : WithTop ℤ) ≤ rootDistance (a : ℚ_[3]) (b : ℚ_[3]))
    (hL' : (H : WithTop ℤ) ≤ rootDistance (a' : ℚ_[3]) (b' : ℚ_[3])) :
    f3UnitHaar.map (f3TruncatedPairObservation a b H) =
      f3UnitHaar.map (f3TruncatedPairObservation a' b' H) := by
  have hpair (x y : ℤ_[3])
      (hxy : (H : WithTop ℤ) ≤ rootDistance (x : ℚ_[3]) (y : ℚ_[3])) :
      f3TruncatedPairObservation x y H =
        (fun z : WithTop ℤ => (z, z)) ∘ f3TruncatedDepthObservation x H := by
    funext d
    apply Prod.ext
    · rfl
    · exact (truncatedRootDepth_eq_of_le_distance (d := (d : ℚ_[3])) hxy).symm
  have hdiag : Measurable (fun z : WithTop ℤ => (z, z)) :=
    measurable_id.prodMk measurable_id
  rw [hpair a b hL, hpair a' b' hL',
    ← Measure.map_map hdiag (f3TruncatedDepthObservation_measurable a H),
    ← Measure.map_map hdiag (f3TruncatedDepthObservation_measurable a' H),
    f3UnitHaar_truncatedDepth_map_eq ha ha' H]

/-- Every finite batch of actual complete samples has the same observation law. -/
theorem f3UnitHaar_truncatedPair_batch_map_eq {a b a' b' : ℤ_[3]}
    (ha : IsUnit a) (hb : IsUnit b) (ha' : IsUnit a') (hb' : IsUnit b')
    {H : ℕ} (hH : 1 ≤ H)
    (hL : (H : WithTop ℤ) ≤ rootDistance (a : ℚ_[3]) (b : ℚ_[3]))
    (hL' : (H : WithTop ℤ) ≤ rootDistance (a' : ℚ_[3]) (b' : ℚ_[3])) (T : ℕ) :
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).map
        (fun d t => f3TruncatedPairObservation a b H (d t)) =
      (Measure.pi (fun _ : Fin T => f3UnitHaar)).map
        (fun d t => f3TruncatedPairObservation a' b' H (d t)) := by
  have hfa : ∀ _t : Fin T, AEMeasurable (f3TruncatedPairObservation a b H) f3UnitHaar :=
    fun _ => (f3TruncatedPairObservation_measurable a b H).aemeasurable
  have hfb : ∀ _t : Fin T, AEMeasurable (f3TruncatedPairObservation a' b' H) f3UnitHaar :=
    fun _ => (f3TruncatedPairObservation_measurable a' b' H).aemeasurable
  rw [Measure.pi_map_pi hfa, Measure.pi_map_pi hfb]
  simp_rw [f3UnitHaar_truncatedPair_map_eq ha hb ha' hb' hH hL hL']

/-- The same actual two-output observation in the original fixed configuration. -/
def f3SharedRootPairObservation (C : F3SharedRootConfig 2) (H : ℕ) (d : ℤ_[3]) :
    WithTop ℤ × WithTop ℤ :=
  (truncatedRootDepth H (d : ℚ_[3]) (C.root 0),
    truncatedRootDepth H (d : ℚ_[3]) (C.root 1))

/-- Original-model nonidentifiability for every finite observation batch. -/
theorem f3SharedRootConfig_truncatedPair_batch_law_eq (C C' : F3SharedRootConfig 2)
    (_hbase : C.baseDepth = C'.baseDepth) {H : ℕ} (hH : 1 ≤ H)
    (hL : (H : WithTop ℤ) ≤ rootDistance (C.root 0) (C.root 1))
    (hL' : (H : WithTop ℤ) ≤ rootDistance (C'.root 0) (C'.root 1)) (T : ℕ) :
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).map
        (fun d t => f3SharedRootPairObservation C H (d t)) =
      (Measure.pi (fun _ : Fin T => f3UnitHaar)).map
        (fun d t => f3SharedRootPairObservation C' H (d t)) := by
  have hd : (H : WithTop ℤ) ≤ rootDistance (f3SharedRootUnit C 0 : ℚ_[3])
      (f3SharedRootUnit C 1 : ℚ_[3]) := by
    simpa only [f3SharedRootUnit_coe] using hL
  have hd' : (H : WithTop ℤ) ≤ rootDistance (f3SharedRootUnit C' 0 : ℚ_[3])
      (f3SharedRootUnit C' 1 : ℚ_[3]) := by
    simpa only [f3SharedRootUnit_coe] using hL'
  simpa only [f3TruncatedPairObservation, f3TruncatedDepthObservation,
    f3SharedRootPairObservation, f3SharedRootUnit_coe] using
    f3UnitHaar_truncatedPair_batch_map_eq (f3SharedRootUnit_isUnit C 0)
      (f3SharedRootUnit_isUnit C 1) (f3SharedRootUnit_isUnit C' 0)
      (f3SharedRootUnit_isUnit C' 1) hH hd hd' T

/-- In particular, true distance H and a strictly larger distance cannot be
separated by the full law of any finite H-truncated observation batch alone. -/
theorem f3SharedRootConfig_truncatedPair_H_vs_higher (C C' : F3SharedRootConfig 2)
    (hbase : C.baseDepth = C'.baseDepth) {H K : ℕ} (hH : 1 ≤ H) (hHK : H < K)
    (hL : rootDistance (C.root 0) (C.root 1) = (H : WithTop ℤ))
    (hL' : rootDistance (C'.root 0) (C'.root 1) = (K : WithTop ℤ)) (T : ℕ) :
    (Measure.pi (fun _ : Fin T => f3UnitHaar)).map
        (fun d t => f3SharedRootPairObservation C H (d t)) =
      (Measure.pi (fun _ : Fin T => f3UnitHaar)).map
        (fun d t => f3SharedRootPairObservation C' H (d t)) := by
  apply f3SharedRootConfig_truncatedPair_batch_law_eq C C' hbase hH _ _ T
  · rw [hL]
  · rw [hL']
    exact_mod_cast hHK.le

end

end OmegaBalance
