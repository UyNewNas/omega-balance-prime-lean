import OmegaBalance.F3BFTBCRTShift

namespace OmegaBalance

/--
From one finite offset bound, choose auxiliary primes and a CRT representative
whose excluded affine values are all composite, while preserving nondivisibility
at every protected tuple offset.
-/
theorem bftb_exists_composite_crt_shift_from_bound
    {T H : Finset ℕ} {g B : ℕ}
    (hg : 0 < g) (hgB : g ≤ B)
    (hT : ∀ t ∈ T, t ≤ B)
    (hH : ∀ h ∈ H, h ≤ B)
    (hdisj : Disjoint T H) :
    ∃ r A : ℕ,
      (∀ t ∈ T, Nat.nth Nat.Prime (r + t) ∣ g * A + t) ∧
      (∀ t ∈ T, ∀ h ∈ H,
        ¬ Nat.nth Nat.Prime (r + t) ∣ g * A + h) ∧
      (∀ t ∈ T, ¬ (g * A + t).Prime) := by
  obtain ⟨r, A, hdiv, hprotect⟩ :=
    bftb_exists_crt_shift_from_bound hg hgB hT hH hdisj
  let q : ℕ → ℕ := fun t => Nat.nth Nat.Prime (r + t)
  let A' : ℕ := A + T.prod q * 2
  have hqprime : ∀ t ∈ T, (q t).Prime := by
    intro t ht
    exact bftbAuxPrime_prime r t
  refine ⟨r, A', ?_, ?_, ?_⟩
  · simpa [q, A'] using
      (bftb_crt_shift_product_preserves_divisors
        (T := T) (g := g) (A := A) (N := 2) q hdiv)
  · simpa [q, A'] using
      (bftb_crt_shift_product_preserves_protected
        (T := T) (H := H) (g := g) (A := A) (N := 2) q hprotect)
  · simpa [q, A'] using
      (bftb_crt_two_product_shift_forces_composite
        (T := T) (g := g) (A := A) q hg hqprime hdiv)

end OmegaBalance
