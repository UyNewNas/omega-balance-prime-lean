import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Order.MinMax
import Mathlib.Tactic.Ring

/-!
# Deterministic certificates in the F₃ shared-root model

This file covers the deterministic parts of F3-REC-1 and F3-REC-4:
REC-L1, REC-L2, the single-pair rule REC-L4, and REC-L11.  The roots are
actual elements of `ℚ_[3]`, and the valuation takes values in `WithTop ℤ`.
In particular, a sample exactly at a root has depth `⊤`, not zero.

The paper model is `R_i = v₃(d - α_i)`, `D_i = b + R_i`, and
`L_ij = v₃(α_i - α_j)`.  `F3SharedRootConfig` records the paper's positive
base depth and distinct, congruent three-adic unit roots; `f3SharedRootDepth`
is its transparent `D_i` coordinate.  The valuation adapters are stronger:
their deterministic conclusions hold for arbitrary three-adic points.

This does not identify these model coordinates with integer prime products,
construct roots for those products, or establish a sampling law.  In
particular, the probabilistic clauses of F3-REC-1/F3-REC-4 and the waiting
time, prime-transfer, and root-tree conclusions are outside this file.

The core proofs reuse the locked mathlib `AddValuation.map_sub` and
`AddValuation.map_add_of_distinct_val`; no valuation theory is reproved.
-/

namespace OmegaBalance

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The excess depth `R = v₃(d - α)`, including infinite depth at a root. -/
def rootDepth (d α : ℚ_[3]) : WithTop ℤ :=
  Padic.addValuation (d - α)

/-- The distance exponent `L = v₃(α - β)` between two actual three-adic roots. -/
def rootDistance (α β : ℚ_[3]) : WithTop ℤ :=
  Padic.addValuation (α - β)

/-- The extended valuation uses the paper's infinite-depth convention. -/
theorem rootDepth_eq_top_iff (d α : ℚ_[3]) :
    rootDepth d α = ⊤ ↔ d = α := by
  change Padic.addValuation (d - α) = ⊤ ↔ d = α
  rw [AddValuation.top_iff, sub_eq_zero]

/-- Away from a root, the depth is the usual integer-valued Padic valuation. -/
theorem rootDepth_eq_valuation {d α : ℚ_[3]} (h : d ≠ α) :
    rootDepth d α = ((d - α).valuation : WithTop ℤ) :=
  Padic.addValuation.apply (sub_ne_zero.mpr h)

/-- Distinct roots have a finite distance exponent, even if a sample hits a root. -/
theorem rootDistance_ne_top {α β : ℚ_[3]} (h : α ≠ β) :
    rootDistance α β ≠ ⊤ :=
  (AddValuation.ne_top_iff Padic.addValuation).2 (sub_ne_zero.mpr h)

/-- REC-L1: every observed minimum is a lower bound on the root distance exponent. -/
theorem rootDepth_min_le_distance (d α β : ℚ_[3]) :
    min (rootDepth d α) (rootDepth d β) ≤ rootDistance α β := by
  change min (Padic.addValuation (d - α)) (Padic.addValuation (d - β)) ≤
    Padic.addValuation (α - β)
  calc
    min (Padic.addValuation (d - α)) (Padic.addValuation (d - β))
        ≤ Padic.addValuation ((d - β) - (d - α)) := by
          simpa only [min_comm] using
            (Padic.addValuation.map_sub (d - β) (d - α))
    _ = Padic.addValuation (α - β) := by congr 1; ring

/-- REC-L2 / deterministic F3-REC-1: unequal depths give the exact root distance. -/
theorem rootDepth_min_eq_distance_of_ne {d α β : ℚ_[3]}
    (h : rootDepth d α ≠ rootDepth d β) :
    rootDistance α β = min (rootDepth d α) (rootDepth d β) := by
  change Padic.addValuation (d - α) ≠ Padic.addValuation (d - β) at h
  change Padic.addValuation (α - β) =
    min (Padic.addValuation (d - α)) (Padic.addValuation (d - β))
  have hne : Padic.addValuation (d - β) ≠ Padic.addValuation (-(d - α)) := by
    simpa only [AddValuation.map_neg] using h.symm
  calc
    Padic.addValuation (α - β) =
        Padic.addValuation ((d - β) + -(d - α)) := by congr 1; ring
    _ = min (Padic.addValuation (d - β)) (Padic.addValuation (-(d - α))) :=
      Padic.addValuation.map_add_of_distinct_val hne
    _ = min (Padic.addValuation (d - α)) (Padic.addValuation (d - β)) := by
      rw [AddValuation.map_neg, min_comm]

/-- One exact-depth observation returns a certificate only when the depths differ. -/
noncomputable def depthCertificate (r s : WithTop ℤ) : Option (WithTop ℤ) :=
  if r = s then none else some (min r s)

/-- REC-L4: every value emitted by the unequal-depth rule is correct. -/
theorem depthCertificate_sound {d α β : ℚ_[3]} {l : WithTop ℤ}
    (h : depthCertificate (rootDepth d α) (rootDepth d β) = some l) :
    rootDistance α β = l := by
  classical
  by_cases heq : rootDepth d α = rootDepth d β
  · simp [depthCertificate, heq] at h
  · have hl : min (rootDepth d α) (rootDepth d β) = l := by
      simpa [depthCertificate, heq] using h
    exact (rootDepth_min_eq_distance_of_ne heq).trans hl

/-- Certificates agree even when the roots move, provided their distance stays fixed. -/
theorem depthCertificate_consistent {d e α β α' β' : ℚ_[3]} {l l' : WithTop ℤ}
    (hfixed : rootDistance α β = rootDistance α' β')
    (h : depthCertificate (rootDepth d α) (rootDepth d β) = some l)
    (h' : depthCertificate (rootDepth e α') (rootDepth e β') = some l') :
    l = l' :=
  (depthCertificate_sound h).symm.trans (hfixed.trans (depthCertificate_sound h'))

/-- The observed depth `Y = min(R,H)` at finite precision `H`. -/
def truncatedRootDepth (H : ℕ) (d α : ℚ_[3]) : WithTop ℤ :=
  min (rootDepth d α) (H : WithTop ℤ)

/-- The correct reconstruction target is `min(L,H)`, not the untruncated distance. -/
def truncatedRootDistance (H : ℕ) (α β : ℚ_[3]) : WithTop ℤ :=
  min (rootDistance α β) (H : WithTop ℤ)

/-- REC-L11, unequal case: distinct truncated observations certify a distance below `H`. -/
theorem truncatedRootDepth_ne_certificate {H : ℕ} {d α β : ℚ_[3]}
    (h : truncatedRootDepth H d α ≠ truncatedRootDepth H d β) :
    rootDistance α β = min (truncatedRootDepth H d α) (truncatedRootDepth H d β) ∧
      min (truncatedRootDepth H d α) (truncatedRootDepth H d β) < (H : WithTop ℤ) := by
  have hraw : rootDepth d α ≠ rootDepth d β := by
    intro heq
    apply h
    simp only [truncatedRootDepth, heq]
  have hdist := rootDepth_min_eq_distance_of_ne hraw
  change min (rootDepth d α) (H : WithTop ℤ) ≠
    min (rootDepth d β) (H : WithTop ℤ) at h
  change rootDistance α β =
      min (min (rootDepth d α) (H : WithTop ℤ))
        (min (rootDepth d β) (H : WithTop ℤ)) ∧
    min (min (rootDepth d α) (H : WithTop ℤ))
      (min (rootDepth d β) (H : WithTop ℤ)) < (H : WithTop ℤ)
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hsmall := min_lt_min_left_iff.mp hlt
    have hmin : min (min (rootDepth d α) (H : WithTop ℤ))
        (min (rootDepth d β) (H : WithTop ℤ)) = rootDepth d α :=
      (min_eq_left hlt.le).trans (min_eq_left hsmall.2.le)
    constructor
    · exact (hdist.trans (min_eq_left hsmall.1.le)).trans hmin.symm
    · rw [hmin]
      exact hsmall.2
  · have hsmall := min_lt_min_left_iff.mp hgt
    have hmin : min (min (rootDepth d α) (H : WithTop ℤ))
        (min (rootDepth d β) (H : WithTop ℤ)) = rootDepth d β :=
      (min_eq_right hgt.le).trans (min_eq_left hsmall.2.le)
    constructor
    · exact (hdist.trans (min_eq_right hsmall.1.le)).trans hmin.symm
    · rw [hmin]
      exact hsmall.2

/-- REC-L11, saturated case: two observations equal to `H` certify `min(L,H)=H`. -/
theorem truncatedRootDepth_saturated_certificate {H : ℕ} {d α β : ℚ_[3]}
    (hα : truncatedRootDepth H d α = (H : WithTop ℤ))
    (hβ : truncatedRootDepth H d β = (H : WithTop ℤ)) :
    (H : WithTop ℤ) ≤ rootDistance α β ∧
      truncatedRootDistance H α β = (H : WithTop ℤ) := by
  have hrα : (H : WithTop ℤ) ≤ rootDepth d α := min_eq_right_iff.mp hα
  have hrβ : (H : WithTop ℤ) ≤ rootDepth d β := min_eq_right_iff.mp hβ
  have hdist : (H : WithTop ℤ) ≤ rootDistance α β :=
    (le_min hrα hrβ).trans (rootDepth_min_le_distance d α β)
  exact ⟨hdist, min_eq_right hdist⟩

/-- The paper's finite-precision rule: unequal values or joint saturation certify;
equal unsaturated values remain unknown. Inputs are the truncated observations. -/
noncomputable def truncatedDepthCertificate (H : ℕ) (y z : WithTop ℤ) :
    Option (WithTop ℤ) :=
  if y = z then
    if y = (H : WithTop ℤ) then some (H : WithTop ℤ) else none
  else some (min y z)

/-- Deterministic F3-REC-4: every emitted truncated certificate is exactly `min(L,H)`. -/
theorem truncatedDepthCertificate_sound {H : ℕ} {d α β : ℚ_[3]} {l : WithTop ℤ}
    (h : truncatedDepthCertificate H (truncatedRootDepth H d α)
      (truncatedRootDepth H d β) = some l) :
    truncatedRootDistance H α β = l := by
  classical
  by_cases heq : truncatedRootDepth H d α = truncatedRootDepth H d β
  · by_cases hsat : truncatedRootDepth H d α = (H : WithTop ℤ)
    · have hl : (H : WithTop ℤ) = l := by
        simpa [truncatedDepthCertificate, heq, hsat] using h
      have hsat' : truncatedRootDepth H d β = (H : WithTop ℤ) := heq.symm.trans hsat
      exact (truncatedRootDepth_saturated_certificate hsat hsat').2.trans hl
    · simp [truncatedDepthCertificate, heq, hsat] at h
  · have hl : min (truncatedRootDepth H d α) (truncatedRootDepth H d β) = l := by
      simpa [truncatedDepthCertificate, heq] using h
    have hc := truncatedRootDepth_ne_certificate heq
    change min (rootDistance α β) (H : WithTop ℤ) = l
    rw [hc.1, min_eq_left hc.2.le]
    exact hl

/-- The paper's actual shared-root model assumptions, without a sampling hypothesis. -/
structure F3SharedRootConfig (m : ℕ) where
  baseDepth : ℕ
  one_le_baseDepth : 1 ≤ baseDepth
  two_le_card : 2 ≤ m
  root : Fin m → ℚ_[3]
  root_unit : ∀ i, Padic.addValuation (root i) = 0
  root_injective : Function.Injective root
  roots_same_residue : ∀ i j, (1 : WithTop ℤ) ≤ rootDistance (root i) (root j)

/-- The source model's total output depth `D_i = b + v₃(d - α_i)`.
This coordinate is not asserted here to equal `f3` of an integer prime product. -/
def f3SharedRootDepth {m : ℕ} (C : F3SharedRootConfig m) (d : ℚ_[3]) (i : Fin m) :
    WithTop ℤ :=
  (C.baseDepth : WithTop ℤ) + rootDepth d (C.root i)

/-- F3-REC-1 on the paper's domain, with a finite certified distance for distinct roots. -/
theorem f3SharedRootDepth_certificate {m : ℕ} (C : F3SharedRootConfig m)
    (d : ℚ_[3]) (_hd : Padic.addValuation d = 0) {i j : Fin m} (hij : i ≠ j)
    {l : WithTop ℤ}
    (h : depthCertificate (rootDepth d (C.root i)) (rootDepth d (C.root j)) = some l) :
    rootDistance (C.root i) (C.root j) = l ∧ l ≠ ⊤ := by
  have hs := depthCertificate_sound h
  refine ⟨hs, ?_⟩
  rw [← hs]
  exact rootDistance_ne_top (fun heq => hij (C.root_injective heq))

/-- F3-REC-4 on the paper's domain and positive precision, with the truncated target. -/
theorem f3SharedRootDepth_truncatedCertificate {m : ℕ} (C : F3SharedRootConfig m)
    (d : ℚ_[3]) (_hd : Padic.addValuation d = 0) {i j : Fin m} (_hij : i ≠ j)
    (H : ℕ) (_hH : 1 ≤ H) {l : WithTop ℤ}
    (h : truncatedDepthCertificate H (truncatedRootDepth H d (C.root i))
      (truncatedRootDepth H d (C.root j)) = some l) :
    truncatedRootDistance H (C.root i) (C.root j) = l :=
  truncatedDepthCertificate_sound h

end OmegaBalance
