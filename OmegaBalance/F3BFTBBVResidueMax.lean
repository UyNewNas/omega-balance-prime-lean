import OmegaBalance.F3BFTBBVNormalization
import Mathlib.Data.ZMod.Units

namespace OmegaBalance

/--
Li-to-pi main-term normalization after taking the finite supremum over unit
residue classes. This is the residue-max layer used by the PrimeGaps
Bombieri--Vinogradov formulation.
-/
theorem bftb_iSup_abs_main_term_change_totient
    {q : ℕ} (hq : 0 < q) (x : (ZMod q)ˣ → ℝ) (li pi : ℝ) :
    (⨆ a : (ZMod q)ˣ, |x a - pi / (q.totient : ℝ)|) ≤
      (⨆ a : (ZMod q)ˣ, |x a - li / (q.totient : ℝ)|) +
        |li - pi| / (q.totient : ℝ) := by
  have hbdd :
      BddAbove (Set.range fun a : (ZMod q)ˣ =>
        |x a - li / (q.totient : ℝ)|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  refine ciSup_le fun a => ?_
  calc
    |x a - pi / (q.totient : ℝ)|
        ≤ |x a - li / (q.totient : ℝ)| +
            |li - pi| / (q.totient : ℝ) :=
      bftb_abs_main_term_change_totient hq (x a) li pi
    _ ≤ (⨆ b : (ZMod q)ˣ, |x b - li / (q.totient : ℝ)|) +
          |li - pi| / (q.totient : ℝ) := by
      exact add_le_add_right (le_ciSup hbdd a) _

/--
Sum the unit-residue supremum normalization over a finite positive modulus
range. The residue type depends on q exactly as in PrimeGaps.
-/
theorem bftb_sum_iSup_abs_main_term_change_totient
    (S : Finset ℕ) (hS : ∀ q ∈ S, 0 < q)
    (x : ∀ q : ℕ, (ZMod q)ˣ → ℝ) (li pi : ℝ) :
    (∑ q ∈ S, ⨆ a : (ZMod q)ˣ,
        |x q a - pi / (q.totient : ℝ)|) ≤
      (∑ q ∈ S, ⨆ a : (ZMod q)ˣ,
        |x q a - li / (q.totient : ℝ)|) +
        ∑ q ∈ S, |li - pi| / (q.totient : ℝ) := by
  calc
    (∑ q ∈ S, ⨆ a : (ZMod q)ˣ,
        |x q a - pi / (q.totient : ℝ)|)
        ≤ ∑ q ∈ S,
            ((⨆ a : (ZMod q)ˣ,
                |x q a - li / (q.totient : ℝ)|) +
              |li - pi| / (q.totient : ℝ)) := by
      exact Finset.sum_le_sum fun q hq =>
        bftb_iSup_abs_main_term_change_totient
          (hS q hq) (x q) li pi
    _ = (∑ q ∈ S, ⨆ a : (ZMod q)ˣ,
          |x q a - li / (q.totient : ℝ)|) +
        ∑ q ∈ S, |li - pi| / (q.totient : ℝ) := by
      rw [Finset.sum_add_distrib]

end OmegaBalance
