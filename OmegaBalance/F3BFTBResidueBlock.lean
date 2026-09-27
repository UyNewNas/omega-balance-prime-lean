import OmegaBalance.F3BFTBOrderedBlock

namespace OmegaBalance

/--
Every element of the ordered prefix block stays in the prescribed residue
class whenever the affine coefficient is divisible by the modulus and every
selected offset has that residue.
-/
theorem bftb_consecutivePrimeBlock_prefix_modEq
    {a D g n lo hi L : ℕ} {S : Finset ℕ}
    (hLS : L ≤ S.card)
    (hDg : D ∣ g)
    (hres : ∀ u ∈ S, u ≡ a [MOD D]) :
    ∀ p ∈
      (List.ofFn fun i : Fin L =>
        g * n + S.orderEmbOfFin rfl
          ⟨i, lt_of_lt_of_le i.isLt hLS⟩),
      p ≡ a [MOD D] := by
  rw [List.forall_mem_ofFn_iff]
  intro i
  let j : Fin S.card :=
    ⟨i, lt_of_lt_of_le i.isLt hLS⟩
  have hjS : S.orderEmbOfFin rfl j ∈ S :=
    S.orderEmbOfFin_mem rfl j
  have hzero : g * n ≡ 0 [MOD D] := by
    rw [Nat.modEq_zero_iff_dvd]
    exact dvd_mul_of_dvd_left hDg n
  simpa [j] using hzero.add (hres (S.orderEmbOfFin rfl j) hjS)

/--
Offsets lying in [lo,hi] give an explicit diameter bound hi-lo for the
corresponding ordered affine prefix block.
-/
theorem bftb_consecutivePrimeBlock_prefix_diameter
    {g n lo hi L : ℕ} {S : Finset ℕ}
    (hLS : L ≤ S.card)
    (hSI : S ⊆ Finset.Icc lo hi) :
    ListDiameterLe
      (List.ofFn fun i : Fin L =>
        g * n + S.orderEmbOfFin rfl
          ⟨i, lt_of_lt_of_le i.isLt hLS⟩)
      (hi - lo) := by
  simp only [ListDiameterLe, List.forall_mem_ofFn_iff]
  intro i j
  let ii : Fin S.card :=
    ⟨i, lt_of_lt_of_le i.isLt hLS⟩
  let jj : Fin S.card :=
    ⟨j, lt_of_lt_of_le j.isLt hLS⟩
  have hiiS : S.orderEmbOfFin rfl ii ∈ S :=
    S.orderEmbOfFin_mem rfl ii
  have hjjS : S.orderEmbOfFin rfl jj ∈ S :=
    S.orderEmbOfFin_mem rfl jj
  have hii := Finset.mem_Icc.mp (hSI hiiS)
  have hjj := Finset.mem_Icc.mp (hSI hjjS)
  dsimp [ii, jj] at hii hjj ⊢
  omega

/--
Package an exact affine prime pattern with at least L selected offsets into a
genuine bounded consecutive-prime run in one residue class. This is a finite
assembly theorem: no Maynard--Tao or BFTB infinitude statement is assumed.
-/
theorem bftb_consecutivePrimeRunInClassBounded_of_exact_prefix
    {a D g n lo hi L B : ℕ} {S : Finset ℕ}
    (hLS : L ≤ S.card)
    (hSI : S ⊆ Finset.Icc lo hi)
    (hexact : ∀ u ∈ Finset.Icc lo hi,
      (g * n + u).Prime ↔ u ∈ S)
    (hDg : D ∣ g)
    (hres : ∀ u ∈ S, u ≡ a [MOD D])
    (hB : B < g * n) :
    ConsecutivePrimeRunInClassBounded a D L B (hi - lo) := by
  let ps : List ℕ :=
    List.ofFn fun i : Fin L =>
      g * n + S.orderEmbOfFin rfl
        ⟨i, lt_of_lt_of_le i.isLt hLS⟩
  refine ⟨ps, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ps] using
      (bftb_consecutivePrimeBlock_prefix_length
        (g := g) (n := n) (lo := lo) (hi := hi) (S := S) hLS)
  · simpa [ps] using
      (bftb_consecutivePrimeBlock_prefix
        (g := g) (n := n) (lo := lo) (hi := hi) (S := S)
        hLS hSI hexact)
  · dsimp [ps]
    rw [List.forall_mem_ofFn_iff]
    intro i
    omega
  · simpa [ps] using
      (bftb_consecutivePrimeBlock_prefix_modEq
        (a := a) (D := D) (g := g) (n := n)
        (lo := lo) (hi := hi) (S := S) hLS hDg hres)
  · simpa [ps] using
      (bftb_consecutivePrimeBlock_prefix_diameter
        (g := g) (n := n) (lo := lo) (hi := hi) (S := S)
        hLS hSI)

end OmegaBalance
