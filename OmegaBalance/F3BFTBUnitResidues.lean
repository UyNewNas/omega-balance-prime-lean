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

end OmegaBalance
