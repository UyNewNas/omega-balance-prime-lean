import OmegaBalance.F3BFTBBVResidueMax
import Mathlib.Data.ZMod.Units

namespace OmegaBalance

/--
Canonical reduced residues in the Liu--Wang convention: representatives
`0 ≤ l < q` coprime to `q`. In particular the modulus-one set is `{0}`,
while the modulus-zero set is empty.
-/
def bftbUnitResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun l => l.Coprime q)

@[simp] theorem mem_bftbUnitResidues {q l : ℕ} :
    l ∈ bftbUnitResidues q ↔ l < q ∧ l.Coprime q := by
  simp [bftbUnitResidues]

@[simp] theorem bftbUnitResidues_zero :
    bftbUnitResidues 0 = ∅ := by
  simp [bftbUnitResidues]

@[simp] theorem bftbUnitResidues_one :
    bftbUnitResidues 1 = {0} := by
  ext l
  simp [bftbUnitResidues]

/--
For every positive modulus, taking the canonical natural representative of a
unit lands in the Liu--Wang reduced-residue finset.
-/
theorem bftb_unit_val_mem_residues
    {q : ℕ} (hq : 0 < q) (u : (ZMod q)ˣ) :
    (u : ZMod q).val ∈ bftbUnitResidues q := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact (mem_bftbUnitResidues).2
    ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩

/--
The canonical reduced residues modulo a positive `q` are equivalent to the
units of `ZMod q`. This is the finite-index bridge between Liu--Wang's
`range q |>.filter Coprime` convention and PrimeGaps' unit-indexed supremum.
-/
noncomputable def bftbUnitResidueEquiv (q : ℕ) (hq : 0 < q) :
    {l : ℕ // l ∈ bftbUnitResidues q} ≃ (ZMod q)ˣ := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  refine
    { toFun := fun l =>
        ZMod.unitOfCoprime l.1 ((mem_bftbUnitResidues.mp l.2).2)
      invFun := fun u => ⟨(u : ZMod q).val, bftb_unit_val_mem_residues hq u⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro l
    apply Subtype.ext
    change (ZMod.unitOfCoprime l.1 ((mem_bftbUnitResidues.mp l.2).2) :
      ZMod q).val = l.1
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt ((mem_bftbUnitResidues.mp l.2).1)]
  · intro u
    apply Units.ext
    change ((((u : ZMod q).val : ℕ) : ZMod q)) = (u : ZMod q)
    exact ZMod.natCast_zmod_val _

/--
Every unit-indexed score can be pulled back to canonical Liu--Wang residues
without changing its range.
-/
theorem range_score_unit_eq_range_residue
    {q : ℕ} (hq : 0 < q) (score : (ZMod q)ˣ → ℝ) :
    Set.range score =
      Set.range (fun l : {l : ℕ // l ∈ bftbUnitResidues q} =>
        score (bftbUnitResidueEquiv q hq l)) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(bftbUnitResidueEquiv q hq).symm u, ?_⟩
    simp
  · rintro ⟨l, rfl⟩
    exact ⟨bftbUnitResidueEquiv q hq l, rfl⟩

/-- The unit obtained from a canonical residue has exactly that residue as its `ZMod` value. -/
theorem bftbUnitResidueEquiv_val
    {q : ℕ} (hq : 0 < q)
    (l : {l : ℕ // l ∈ bftbUnitResidues q}) :
    ((bftbUnitResidueEquiv q hq l : (ZMod q)ˣ) : ZMod q).val = l.1 := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  change (ZMod.unitOfCoprime l.1 ((mem_bftbUnitResidues.mp l.2).2) :
    ZMod q).val = l.1
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt ((mem_bftbUnitResidues.mp l.2).1)]

/-- Finite maximum in the canonical reduced-residue presentation. -/
noncomputable def bftbCanonicalResidueMax (q : ℕ) (score : ℕ → ℝ) : ℝ :=
  let S := bftbUnitResidues q
  if h : S.Nonempty then
    (S.image score).max' (Finset.image_nonempty.mpr h)
  else 0

/-- For positive q, the canonical finite max is exactly the unit-indexed supremum. -/
theorem bftbCanonicalResidueMax_eq_iSup
    {q : ℕ} (hq : 0 < q) (score : ℕ → ℝ) :
    bftbCanonicalResidueMax q score =
      ⨆ u : (ZMod q)ˣ, score (u : ZMod q).val := by
  let S := bftbUnitResidues q
  have hS : S.Nonempty := by
    let l := (bftbUnitResidueEquiv q hq).symm (1 : (ZMod q)ˣ)
    exact ⟨l.1, l.2⟩
  rw [bftbCanonicalResidueMax, dif_pos hS]
  apply le_antisymm
  · have hmem : (S.image score).max' (Finset.image_nonempty.mpr hS) ∈ S.image score :=
      Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨l, hl, hscore⟩
    rw [← hscore]
    have hbdd :
        BddAbove (Set.range fun u : (ZMod q)ˣ => score (u : ZMod q).val) :=
      Set.Finite.bddAbove (Set.finite_range _)
    let r : {l : ℕ // l ∈ bftbUnitResidues q} := ⟨l, hl⟩
    have hval :
        ((bftbUnitResidueEquiv q hq r : (ZMod q)ˣ) : ZMod q).val = l :=
      bftbUnitResidueEquiv_val hq r
    rw [← hval]
    exact le_ciSup hbdd (bftbUnitResidueEquiv q hq r)
  · refine ciSup_le fun u => ?_
    have hmem : (u : ZMod q).val ∈ S := bftb_unit_val_mem_residues hq u
    exact Finset.le_max' (S.image score) _
      (Finset.mem_image.mpr ⟨(u : ZMod q).val, hmem, rfl⟩)

end OmegaBalance
