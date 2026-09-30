import OmegaBalance.F3RootReconstruction

/-!
# Finite-precision matrix recovery in the F₃ shared-root model

This file implements the deterministic finite-data part of F3-REC-4
(proof Theorem 2.6, REC-L11 and the truncated counterpart of REC-L5).
The input consists only of labelled observations `Y_i = min(R_i,H)`.
A pair is certified by unequal observations OR joint saturation at `H`.
Equal unsaturated observations remain unknown. The target is `min(L_ij,H)`;
the known diagonal is therefore `H`, not the full-precision value `⊤`.

The scan reuses `List.findSome?` and the existing single-observation
`truncatedDepthCertificate_sound`. Actual roots lie in `ℚ_[3]`, with
`WithTop ℤ` depths, so samples hitting roots keep their infinite raw depth.
Moving roots are allowed when their true labelled distances remain fixed.
The paper-domain wrapper retains positive precision and base depth, unit
samples, distinct congruent unit roots and at least two labels.

Complete recovery is equivalent to having a finite witness for every
non-diagonal pair. This is not a guarantee that sampling supplies witnesses.
The recovered matrix determines every threshold cluster at `t ≤ H`, by
reusing the full-precision root-cluster equivalence relation. There is no
claim of recovering true distances above `H`, probabilistic waiting bounds,
prime-product root construction, or fixed-precision prime distribution.
-/

namespace OmegaBalance

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {ι σ : Type*}

/-- The two valid finite-precision witness events, expressed only in observed data. -/
def truncatedDepthWitness (H : ℕ) (y z : WithTop ℤ) : Prop :=
  y ≠ z ∨ (y = (H : WithTop ℤ) ∧ z = (H : WithTop ℤ))

/-- The existing certificate rule succeeds precisely on the two witness events,
and in both cases returns the observed minimum. -/
theorem truncatedDepthCertificate_eq_some_iff (H : ℕ) (y z l : WithTop ℤ) :
    truncatedDepthCertificate H y z = some l ↔
      truncatedDepthWitness H y z ∧ min y z = l := by
  classical
  by_cases heq : y = z
  · subst z
    by_cases hsat : y = (H : WithTop ℤ)
    · simp [truncatedDepthCertificate, truncatedDepthWitness, hsat]
    · simp [truncatedDepthCertificate, truncatedDepthWitness, hsat]
  · simp [truncatedDepthCertificate, truncatedDepthWitness, heq]

/-- Unknown means exactly equal observations away from the saturation value.
For actual truncated inputs this is the equal, strictly below `H` case. -/
theorem truncatedDepthCertificate_eq_none_iff (H : ℕ) (y z : WithTop ℤ) :
    truncatedDepthCertificate H y z = none ↔ y = z ∧ y ≠ (H : WithTop ℤ) := by
  classical
  by_cases heq : y = z
  · subst z
    by_cases hsat : y = (H : WithTop ℤ)
    · simp [truncatedDepthCertificate, hsat]
    · simp [truncatedDepthCertificate, hsat]
  · simp [truncatedDepthCertificate, heq]

/-- Scan finite-precision observations in order, using the existing certificate rule. -/
def truncatedDepthCertificateScan (H : ℕ) (samples : List σ)
    (Y : σ → ι → WithTop ℤ) (i j : ι) : Option (WithTop ℤ) :=
  samples.findSome? (fun s => truncatedDepthCertificate H (Y s i) (Y s j))

/-- The first successful observation is unequal or jointly saturated; every earlier
observation is equal and unsaturated. Its zero-based position is `before.length`. -/
theorem truncatedDepthCertificateScan_first {H : ℕ} {samples : List σ}
    {Y : σ → ι → WithTop ℤ} {i j : ι} {l : WithTop ℤ}
    (h : truncatedDepthCertificateScan H samples Y i j = some l) :
    ∃ before s after, samples = before ++ s :: after ∧
      truncatedDepthWitness H (Y s i) (Y s j) ∧ min (Y s i) (Y s j) = l ∧
      ∀ t ∈ before, Y t i = Y t j ∧ Y t i ≠ (H : WithTop ℤ) := by
  obtain ⟨before, s, after, hlist, hcert, hprior⟩ :=
    List.findSome?_eq_some_iff.mp h
  have hw := (truncatedDepthCertificate_eq_some_iff H (Y s i) (Y s j) l).mp hcert
  exact ⟨before, s, after, hlist, hw.1, hw.2,
    fun t ht => (truncatedDepthCertificate_eq_none_iff H (Y t i) (Y t j)).mp
      (hprior t ht)⟩

/-- A scan remains unknown exactly when all recorded observations are equal and
unsaturated, rather than interpreting missing data as an exact root distance. -/
theorem truncatedDepthCertificateScan_eq_none_iff (H : ℕ) (samples : List σ)
    (Y : σ → ι → WithTop ℤ) (i j : ι) :
    truncatedDepthCertificateScan H samples Y i j = none ↔
      ∀ s ∈ samples, Y s i = Y s j ∧ Y s i ≠ (H : WithTop ℤ) := by
  simp only [truncatedDepthCertificateScan, List.findSome?_eq_none_iff,
    truncatedDepthCertificate_eq_none_iff]

/-- Every emitted value is the actual truncated root distance, also for moving
roots whose true labelled distance is fixed over the observed configurations. -/
theorem truncatedDepthCertificateScan_sound {H : ℕ} {samples : List σ}
    {d : σ → ℚ_[3]} {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]}
    {i j : ι} {l : WithTop ℤ}
    (hfixed : ∀ s ∈ samples, rootDistance (α s i) (α s j) =
      rootDistance (α₀ i) (α₀ j))
    (h : truncatedDepthCertificateScan H samples
      (fun s k => truncatedRootDepth H (d s) (α s k)) i j = some l) :
    truncatedRootDistance H (α₀ i) (α₀ j) = l := by
  obtain ⟨s, hs, hcert⟩ := List.exists_of_findSome?_eq_some h
  have hsound := truncatedDepthCertificate_sound hcert
  change min (rootDistance (α s i) (α s j)) (H : WithTop ℤ) = l at hsound
  rw [hfixed s hs] at hsound
  exact hsound

/-- A pair is recovered iff the actual finite data contain an unequal or jointly
saturated observation. Equal saturated observations must not be discarded. -/
theorem truncatedDepthCertificateScan_recover_iff {H : ℕ} {samples : List σ}
    {d : σ → ℚ_[3]} {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]} (i j : ι)
    (hfixed : ∀ s ∈ samples, rootDistance (α s i) (α s j) =
      rootDistance (α₀ i) (α₀ j)) :
    truncatedDepthCertificateScan H samples
        (fun s k => truncatedRootDepth H (d s) (α s k)) i j =
        some (truncatedRootDistance H (α₀ i) (α₀ j)) ↔
      ∃ s ∈ samples, truncatedDepthWitness H
        (truncatedRootDepth H (d s) (α s i))
        (truncatedRootDepth H (d s) (α s j)) := by
  constructor
  · intro h
    obtain ⟨s, hs, hcert⟩ := List.exists_of_findSome?_eq_some h
    exact ⟨s, hs, ((truncatedDepthCertificate_eq_some_iff H _ _ _).mp hcert).1⟩
  · rintro ⟨s, hs, hw⟩
    cases hscan : truncatedDepthCertificateScan H samples
        (fun t k => truncatedRootDepth H (d t) (α t k)) i j with
    | none =>
      have hnone := (truncatedDepthCertificateScan_eq_none_iff H _ _ _ _).mp hscan s hs
      rcases hw with hne | hsat
      · exact False.elim (hne hnone.1)
      · exact False.elim (hnone.2 hsat.1)
    | some l =>
      have hsound := truncatedDepthCertificateScan_sound hfixed hscan
      exact congrArg some hsound.symm

/-- Partial finite-precision matrix, with known diagonal `min(⊤,H)=H` and
scanned off-diagonal entries. The algorithm does not receive roots or distances. -/
def truncatedDepthCertificateMatrix (H : ℕ) (samples : List σ)
    (Y : σ → ι → WithTop ℤ) : ι → ι → Option (WithTop ℤ) := by
  classical
  exact fun i j => if i = j then some (H : WithTop ℤ) else
    truncatedDepthCertificateScan H samples Y i j

/-- Deterministic finite-precision matrix recovery is equivalent to a valid
finite-data witness for each off-diagonal pair. No diagonal witness is needed. -/
theorem truncatedDepthCertificateMatrix_recover_iff {H : ℕ} {samples : List σ}
    {d : σ → ℚ_[3]} {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]}
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance (α s i) (α s j) = rootDistance (α₀ i) (α₀ j)) :
    truncatedDepthCertificateMatrix H samples
        (fun s k => truncatedRootDepth H (d s) (α s k)) =
        (fun i j => some (truncatedRootDistance H (α₀ i) (α₀ j))) ↔
      ∀ i j, i ≠ j → ∃ s ∈ samples, truncatedDepthWitness H
        (truncatedRootDepth H (d s) (α s i))
        (truncatedRootDepth H (d s) (α s j)) := by
  classical
  constructor
  · intro hmatrix i j hij
    have hentry := congrFun (congrFun hmatrix i) j
    have hscan : truncatedDepthCertificateScan H samples
        (fun s k => truncatedRootDepth H (d s) (α s k)) i j =
        some (truncatedRootDistance H (α₀ i) (α₀ j)) := by
      simpa only [truncatedDepthCertificateMatrix, if_neg hij] using hentry
    exact (truncatedDepthCertificateScan_recover_iff i j
      (fun s hs => hfixed s hs i j)).mp hscan
  · intro hcomplete
    funext i j
    by_cases hij : i = j
    · subst j
      simp [truncatedDepthCertificateMatrix, truncatedRootDistance, rootDistance,
        AddValuation.map_zero]
    · change (if i = j then some (H : WithTop ℤ) else
        truncatedDepthCertificateScan H samples
          (fun s k => truncatedRootDepth H (d s) (α s k)) i j) = _
      rw [if_neg hij]
      exact (truncatedDepthCertificateScan_recover_iff i j
        (fun s hs => hfixed s hs i j)).mpr (hcomplete i j hij)

/-- Truncation preserves exactly the root-cluster tests at thresholds at most `H`.
The precision bound is essential, including on the diagonal. -/
theorem truncatedRootDistance_threshold_iff {H : ℕ} {α β : ℚ_[3]}
    {t : WithTop ℤ} (ht : t ≤ (H : WithTop ℤ)) :
    t ≤ truncatedRootDistance H α β ↔ t ≤ rootDistance α β := by
  change t ≤ min (rootDistance α β) (H : WithTop ℤ) ↔ t ≤ rootDistance α β
  exact ⟨fun h => h.trans (min_le_left _ _), fun h => le_min h ht⟩

/-- Every threshold cluster through precision `H` is recovered from the truncated
matrix, including the boundary threshold `H` and the diagonal. -/
theorem truncatedDepthCertificateMatrix_cluster_iff {H : ℕ} {samples : List σ}
    {d : σ → ℚ_[3]} {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]}
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance (α s i) (α s j) = rootDistance (α₀ i) (α₀ j))
    (hcomplete : ∀ i j, i ≠ j → ∃ s ∈ samples, truncatedDepthWitness H
      (truncatedRootDepth H (d s) (α s i)) (truncatedRootDepth H (d s) (α s j)))
    {t : WithTop ℤ} (ht : t ≤ (H : WithTop ℤ)) (i j : ι) :
    (∃ l, truncatedDepthCertificateMatrix H samples
      (fun s k => truncatedRootDepth H (d s) (α s k)) i j = some l ∧ t ≤ l) ↔
      rootClusterSetoid α₀ t i j := by
  rw [(truncatedDepthCertificateMatrix_recover_iff hfixed).mpr hcomplete]
  change (∃ l, some (truncatedRootDistance H (α₀ i) (α₀ j)) = some l ∧ t ≤ l) ↔
    t ≤ rootDistance (α₀ i) (α₀ j)
  simp only [Option.some.injEq, exists_eq_left']
  exact truncatedRootDistance_threshold_iff ht

/-- Under finite-data completeness, observed cluster tests at `t ≤ H` form the
same equivalence relation as the actual roots, not just isolated pairwise facts. -/
theorem truncatedDepthCertificateMatrix_cluster_equivalence {H : ℕ} {samples : List σ}
    {d : σ → ℚ_[3]} {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]}
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance (α s i) (α s j) = rootDistance (α₀ i) (α₀ j))
    (hcomplete : ∀ i j, i ≠ j → ∃ s ∈ samples, truncatedDepthWitness H
      (truncatedRootDepth H (d s) (α s i)) (truncatedRootDepth H (d s) (α s j)))
    {t : WithTop ℤ} (ht : t ≤ (H : WithTop ℤ)) :
    Equivalence (fun i j => ∃ l, truncatedDepthCertificateMatrix H samples
      (fun s k => truncatedRootDepth H (d s) (α s k)) i j = some l ∧ t ≤ l) := by
  have hc := truncatedDepthCertificateMatrix_cluster_iff hfixed hcomplete ht
  have he := rootDistance_threshold_equivalence α₀ t
  exact ⟨fun i => (hc i i).mpr (he.refl i),
    fun {i j} hij => (hc j i).mpr (he.symm ((hc i j).mp hij)),
    fun {i j k} hij hjk => (hc i k).mpr (he.trans ((hc i j).mp hij) ((hc j k).mp hjk))⟩

/-- Deterministic F3-REC-4 on the original paper's domain, including positive
precision, positive fixed base depth, unit samples and distinct congruent roots.
The necessary-and-sufficient condition contains only finite observed data. -/
theorem f3SharedRootConfig_truncatedMatrix_recover_iff {m : ℕ}
    (C₀ : F3SharedRootConfig m) (C : σ → F3SharedRootConfig m)
    (H : ℕ) (_hH : 1 ≤ H) (samples : List σ) (d : σ → ℚ_[3])
    (_hd : ∀ s ∈ samples, Padic.addValuation (d s) = 0)
    (_hbase : ∀ s ∈ samples, (C s).baseDepth = C₀.baseDepth)
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance ((C s).root i) ((C s).root j) = rootDistance (C₀.root i) (C₀.root j)) :
    truncatedDepthCertificateMatrix H samples
        (fun s i => truncatedRootDepth H (d s) ((C s).root i)) =
        (fun i j => some (truncatedRootDistance H (C₀.root i) (C₀.root j))) ↔
      ∀ i j, i ≠ j → ∃ s ∈ samples, truncatedDepthWitness H
        (truncatedRootDepth H (d s) ((C s).root i))
        (truncatedRootDepth H (d s) ((C s).root j)) :=
  truncatedDepthCertificateMatrix_recover_iff hfixed

end

end OmegaBalance
