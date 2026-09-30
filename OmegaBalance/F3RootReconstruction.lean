import OmegaBalance.F3RootCertificates
import Mathlib.Data.Setoid.Basic
import Init.Data.List.Find

/-!
# Finite certificate recovery in the F₃ shared-root model

This is the deterministic matrix and threshold-cluster part of REC-L5
(F3-REC-2, proof Proposition 2.2).  The algorithm sees only a finite list of
labelled depth vectors.  It keeps the first unequal-depth certificate for
each pair and leaves pairs without a certificate unknown.  The diagonal
is the known value `⊤` of `v₃(0)`.

Soundness is proved for actual `ℚ_[3]` roots, which may move between samples
provided their labelled distance matrix stays fixed.  The final wrapper
retains the paper's `F3SharedRootConfig` hypotheses and unit-valued samples.
No sampling distribution, prime-counting statement, joint-depth probability
formula, or reconstruction of absolute root positions is asserted here.

The scan reuses Lean 4.34's `List.findSome?` and its first-success and
membership theorems.  Its mathematical content reuses the certified
`depthCertificate_sound`; no valuation or list-search foundation is rebuilt.
-/

namespace OmegaBalance

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {ι σ : Type*}

/-- Scan the observations in order, keeping the first exact pair certificate. -/
def depthCertificateScan (samples : List σ) (R : σ → ι → WithTop ℤ) (i j : ι) :
    Option (WithTop ℤ) :=
  samples.findSome? (fun s => depthCertificate (R s i) (R s j))

/-- The returned certificate comes from the first unequal observation.
The list prefix records its position, whose zero-based index is `before.length`. -/
theorem depthCertificateScan_first {samples : List σ} {R : σ → ι → WithTop ℤ}
    {i j : ι} {l : WithTop ℤ} (h : depthCertificateScan samples R i j = some l) :
    ∃ before s after, samples = before ++ s :: after ∧ R s i ≠ R s j ∧
      min (R s i) (R s j) = l ∧ ∀ t ∈ before, R t i = R t j := by
  classical
  obtain ⟨before, s, after, hlist, hcert, hprior⟩ :=
    List.findSome?_eq_some_iff.mp h
  have hne : R s i ≠ R s j := by
    intro heq
    simp [depthCertificate, heq] at hcert
  refine ⟨before, s, after, hlist, hne, ?_, ?_⟩
  · simpa [depthCertificate, hne] using hcert
  · intro t ht
    have htcert := hprior t ht
    by_contra htne
    simp [depthCertificate, htne] at htcert

/-- No certificate means exactly that every recorded observation had equal depths.
It does not assert that the roots coincide or that their distance is large. -/
theorem depthCertificateScan_eq_none_iff (samples : List σ) (R : σ → ι → WithTop ℤ)
    (i j : ι) :
    depthCertificateScan samples R i j = none ↔ ∀ s ∈ samples, R s i = R s j := by
  classical
  simp [depthCertificateScan, List.findSome?_eq_none_iff, depthCertificate]

/-- REC-L5 soundness, including moving roots with a fixed labelled distance matrix. -/
theorem depthCertificateScan_sound {samples : List σ} {d : σ → ℚ_[3]}
    {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]} {i j : ι} {l : WithTop ℤ}
    (hfixed : ∀ s ∈ samples, rootDistance (α s i) (α s j) =
      rootDistance (α₀ i) (α₀ j))
    (h : depthCertificateScan samples (fun s k => rootDepth (d s) (α s k)) i j =
      some l) :
    rootDistance (α₀ i) (α₀ j) = l := by
  obtain ⟨s, hs, hcert⟩ := List.exists_of_findSome?_eq_some h
  exact (hfixed s hs).symm.trans (depthCertificate_sound hcert)

/-- An actual pair is recovered exactly when the finite data contain an unequal
observation.  This is deterministic completeness, not a guarantee of sampling one. -/
theorem depthCertificateScan_recover_iff {samples : List σ} {d : σ → ℚ_[3]}
    {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]} (i j : ι)
    (hfixed : ∀ s ∈ samples, rootDistance (α s i) (α s j) =
      rootDistance (α₀ i) (α₀ j)) :
    depthCertificateScan samples (fun s k => rootDepth (d s) (α s k)) i j =
        some (rootDistance (α₀ i) (α₀ j)) ↔
      ∃ s ∈ samples, rootDepth (d s) (α s i) ≠ rootDepth (d s) (α s j) := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs, hcert⟩ := List.exists_of_findSome?_eq_some h
    refine ⟨s, hs, ?_⟩
    intro heq
    simp [depthCertificate, heq] at hcert
  · rintro ⟨s, hs, hne⟩
    cases hscan : depthCertificateScan samples
        (fun t k => rootDepth (d t) (α t k)) i j with
    | none =>
      exact False.elim (hne ((depthCertificateScan_eq_none_iff _ _ _ _).mp hscan s hs))
    | some l =>
      have hsound := depthCertificateScan_sound hfixed hscan
      exact congrArg some hsound.symm

/-- The observable partial matrix: known infinite diagonal and scanned off-diagonal
entries. Unknown pairs remain `none`, rather than being assigned a numerical value. -/
def depthCertificateMatrix (samples : List σ) (R : σ → ι → WithTop ℤ) :
    ι → ι → Option (WithTop ℤ) := by
  classical
  exact fun i j => if i = j then some ⊤ else depthCertificateScan samples R i j

/-- REC-L5: if every off-diagonal pair has a witness, the entire labelled distance
matrix is recovered, with the true infinite diagonal. -/
theorem depthCertificateMatrix_recover {samples : List σ} {d : σ → ℚ_[3]}
    {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]}
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance (α s i) (α s j) = rootDistance (α₀ i) (α₀ j))
    (hcomplete : ∀ i j, i ≠ j →
      ∃ s ∈ samples, rootDepth (d s) (α s i) ≠ rootDepth (d s) (α s j)) :
    depthCertificateMatrix samples (fun s k => rootDepth (d s) (α s k)) =
      fun i j => some (rootDistance (α₀ i) (α₀ j)) := by
  classical
  funext i j
  by_cases hij : i = j
  · subst j
    simp [depthCertificateMatrix, rootDistance, AddValuation.map_zero]
  · change (if i = j then some ⊤ else depthCertificateScan samples
      (fun s k => rootDepth (d s) (α s k)) i j) = _
    rw [if_neg hij]
    exact (depthCertificateScan_recover_iff i j (fun s hs => hfixed s hs i j)).mpr
      (hcomplete i j hij)

/-- Actual p-adic roots induce an equivalence relation at every distance threshold. -/
theorem rootDistance_threshold_equivalence (α : ι → ℚ_[3]) (t : WithTop ℤ) :
    Equivalence (fun i j => t ≤ rootDistance (α i) (α j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [rootDistance, AddValuation.map_zero]
  · intro i j hij
    change t ≤ Padic.addValuation (α j - α i)
    rw [AddValuation.map_sub_swap]
    exact hij
  · intro i j k hij hjk
    calc
      t ≤ min (rootDepth (α j) (α i)) (rootDepth (α j) (α k)) := by
        apply le_min
        · change t ≤ Padic.addValuation (α j - α i)
          rw [AddValuation.map_sub_swap]
          exact hij
        · exact hjk
      _ ≤ rootDistance (α i) (α k) := rootDepth_min_le_distance (α j) (α i) (α k)

/-- The labelled root clusters at a threshold; a `Setoid` represents the partition. -/
def rootClusterSetoid (α : ι → ℚ_[3]) (t : WithTop ℤ) : Setoid ι where
  r i j := t ≤ rootDistance (α i) (α j)
  iseqv := rootDistance_threshold_equivalence α t

/-- Higher thresholds refine lower-threshold clusters, giving the nested hierarchy. -/
theorem rootClusterSetoid_refines (α : ι → ℚ_[3]) {t u : WithTop ℤ} (htu : t ≤ u) :
    rootClusterSetoid α u ≤ rootClusterSetoid α t := by
  intro i j hij
  exact htu.trans hij

/-- Every cluster test can be performed on the recovered matrix, at any threshold.
This includes the diagonal and does not ask for the roots' absolute positions. -/
theorem depthCertificateMatrix_cluster_iff {samples : List σ} {d : σ → ℚ_[3]}
    {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]}
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance (α s i) (α s j) = rootDistance (α₀ i) (α₀ j))
    (hcomplete : ∀ i j, i ≠ j →
      ∃ s ∈ samples, rootDepth (d s) (α s i) ≠ rootDepth (d s) (α s j))
    (t : WithTop ℤ) (i j : ι) :
    (∃ l, depthCertificateMatrix samples (fun s k => rootDepth (d s) (α s k)) i j =
      some l ∧ t ≤ l) ↔ rootClusterSetoid α₀ t i j := by
  rw [depthCertificateMatrix_recover hfixed hcomplete]
  change (∃ l, some (rootDistance (α₀ i) (α₀ j)) = some l ∧ t ≤ l) ↔
    t ≤ rootDistance (α₀ i) (α₀ j)
  simp only [Option.some.injEq, exists_eq_left']

/-- The recovered threshold relation is itself an equivalence relation, rather
than merely a collection of individually correct pair tests. -/
theorem depthCertificateMatrix_cluster_equivalence {samples : List σ} {d : σ → ℚ_[3]}
    {α : σ → ι → ℚ_[3]} {α₀ : ι → ℚ_[3]}
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance (α s i) (α s j) = rootDistance (α₀ i) (α₀ j))
    (hcomplete : ∀ i j, i ≠ j →
      ∃ s ∈ samples, rootDepth (d s) (α s i) ≠ rootDepth (d s) (α s j))
    (t : WithTop ℤ) :
    Equivalence (fun i j => ∃ l,
      depthCertificateMatrix samples (fun s k => rootDepth (d s) (α s k)) i j =
        some l ∧ t ≤ l) := by
  have hc := depthCertificateMatrix_cluster_iff hfixed hcomplete t
  have he := rootDistance_threshold_equivalence α₀ t
  exact ⟨fun i => (hc i i).mpr (he.refl i),
    fun {i j} hij => (hc j i).mpr (he.symm ((hc i j).mp hij)),
    fun {i j k} hij hjk => (hc i k).mpr (he.trans ((hc i j).mp hij) ((hc j k).mp hjk))⟩

/-- REC-L5 on the paper's domain.  Each configuration retains positive base depth,
distinct congruent unit roots and at least two labels; samples are units.  Moving
roots are allowed, and only their labelled distances are required to stay fixed. -/
theorem f3SharedRootConfig_matrix_recover {m : ℕ} (C₀ : F3SharedRootConfig m)
    (C : σ → F3SharedRootConfig m) (samples : List σ) (d : σ → ℚ_[3])
    (_hd : ∀ s ∈ samples, Padic.addValuation (d s) = 0)
    (_hbase : ∀ s ∈ samples, (C s).baseDepth = C₀.baseDepth)
    (hfixed : ∀ s ∈ samples, ∀ i j,
      rootDistance ((C s).root i) ((C s).root j) = rootDistance (C₀.root i) (C₀.root j))
    (hcomplete : ∀ i j, i ≠ j → ∃ s ∈ samples,
      rootDepth (d s) ((C s).root i) ≠ rootDepth (d s) ((C s).root j)) :
    depthCertificateMatrix samples (fun s i => rootDepth (d s) ((C s).root i)) =
        (fun i j => some (rootDistance (C₀.root i) (C₀.root j))) ∧
      ∀ i j, i ≠ j → rootDistance (C₀.root i) (C₀.root j) ≠ ⊤ := by
  refine ⟨depthCertificateMatrix_recover hfixed hcomplete, ?_⟩
  intro i j hij
  exact rootDistance_ne_top (fun h => hij (C₀.root_injective h))

end

end OmegaBalance
