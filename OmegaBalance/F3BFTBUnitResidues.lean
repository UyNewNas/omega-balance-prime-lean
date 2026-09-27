import OmegaBalance.F3BFTBBVResidueMax
import Mathlib.Data.ZMod.Units

namespace OmegaBalance

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
  simp [bftbUnitResidues, Nat.lt_one_iff]

theorem bftbUnitResidues_eq_image_units_val
    {q : ℕ} (hq : 0 < q) :
    bftbUnitResidues q =
      Finset.univ.image (fun u : (ZMod q)ˣ => (u : ZMod q).val) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  ext l
  constructor
  · intro hl
    rw [mem_bftbUnitResidues] at hl
    rcases hl with ⟨hlt, hcop⟩
    refine Finset.mem_image.mpr
      ⟨ZMod.unitOfCoprime l hcop, Finset.mem_univ _, ?_⟩
    simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨u, _hu, rfl⟩
    rw [mem_bftbUnitResidues]
    exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩

theorem bftbUnitResidues_nonempty {q : ℕ} (hq : 0 < q) :
    (bftbUnitResidues q).Nonempty := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  refine ⟨((1 : (ZMod q)ˣ) : ZMod q).val, ?_⟩
  rw [mem_bftbUnitResidues]
  exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime 1⟩

noncomputable def bftbUnitResidueMax (q : ℕ) (score : ℕ → ℝ) : ℝ :=
  let S := bftbUnitResidues q
  if h : S.Nonempty then
    (S.image score).max' (Finset.image_nonempty.mpr h)
  else 0

@[simp] theorem bftbUnitResidueMax_zero (score : ℕ → ℝ) :
    bftbUnitResidueMax 0 score = 0 := by
  simp [bftbUnitResidueMax]

@[simp] theorem bftbUnitResidueMax_one (score : ℕ → ℝ) :
    bftbUnitResidueMax 1 score = score 0 := by
  simp [bftbUnitResidueMax]

theorem bftbUnitResidueMax_eq_iSup_units
    {q : ℕ} (hq : 0 < q) (score : ℕ → ℝ) :
    bftbUnitResidueMax q score =
      ⨆ u : (ZMod q)ˣ, score (u : ZMod q).val := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hS : (bftbUnitResidues q).Nonempty :=
    bftbUnitResidues_nonempty hq
  rw [bftbUnitResidueMax, dif_pos hS]
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨l, hl, rfl⟩
    rw [bftbUnitResidues_eq_image_units_val hq] at hl
    rcases Finset.mem_image.mp hl with ⟨u, _hu, rfl⟩
    have hbdd :
        BddAbove (Set.range fun v : (ZMod q)ˣ =>
          score (v : ZMod q).val) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_ciSup hbdd u
  · refine ciSup_le fun u => ?_
    exact Finset.le_max'
      ((bftbUnitResidues q).image score)
      (score (u : ZMod q).val)
      (Finset.mem_image.mpr
        ⟨(u : ZMod q).val,
          (mem_bftbUnitResidues.mpr
            ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩),
          rfl⟩)

end OmegaBalance
