import OmegaBalance.F3BFTBCRTComposite

namespace OmegaBalance

/--
Once the product-shift parameter is at least two, every assigned auxiliary
prime is still a proper divisor of its excluded affine value.
-/
theorem bftb_crt_product_shift_proper_of_two_le
    {T : Finset ℕ} {g A N : ℕ} (q : ℕ → ℕ)
    (hg : 0 < g)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hN : 2 ≤ N) :
    ∀ t ∈ T, q t < g * (A + T.prod q * N) + t := by
  intro t ht
  have hQpos : 0 < T.prod q :=
    Finset.prod_pos (fun i hi => (hqprime i hi).pos)
  have hqQ : q t ∣ T.prod q :=
    bftb_crt_modulus_dvd_product q ht
  have hqleQ : q t ≤ T.prod q :=
    Nat.le_of_dvd hQpos hqQ
  have hQlt2Q : T.prod q < T.prod q * 2 := by
    omega
  have h2QleQN : T.prod q * 2 ≤ T.prod q * N :=
    Nat.mul_le_mul_left (T.prod q) hN
  have hQNle : T.prod q * N ≤ A + T.prod q * N := by
    omega
  have hmul :
      A + T.prod q * N ≤ g * (A + T.prod q * N) :=
    Nat.le_mul_of_pos_left _ hg
  have hadd :
      g * (A + T.prod q * N) ≤
        g * (A + T.prod q * N) + t := by
    omega
  exact lt_of_lt_of_le
    (lt_of_le_of_lt hqleQ hQlt2Q)
    (h2QleQN.trans (hQNle.trans (hmul.trans hadd)))

/--
Every sufficiently shifted CRT representative forces all excluded positions
to be composite, not merely divisible by an auxiliary prime.
-/
theorem bftb_crt_product_shift_forces_composite_of_two_le
    {T : Finset ℕ} {g A N : ℕ} (q : ℕ → ℕ)
    (hg : 0 < g)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hdiv : ∀ t ∈ T, q t ∣ g * A + t)
    (hN : 2 ≤ N) :
    ∀ t ∈ T, ¬ (g * (A + T.prod q * N) + t).Prime := by
  apply bftb_crt_divisors_force_composite q hqprime
  · exact bftb_crt_shift_product_preserves_divisors
      (N := N) q hdiv
  · exact bftb_crt_product_shift_proper_of_two_le
      q hg hqprime hN

/--
The finite CRT construction yields an infinite product-shift progression on
which every excluded offset is composite, while all protected nondivisibility
conditions are preserved. The quantified parameter starts at two only to make
properness of the auxiliary divisor completely explicit.
-/
theorem bftb_exists_composite_crt_progression_from_bound
    {T H : Finset ℕ} {g B : ℕ}
    (hg : 0 < g) (hgB : g ≤ B)
    (hT : ∀ t ∈ T, t ≤ B)
    (hH : ∀ h ∈ H, h ≤ B)
    (hdisj : Disjoint T H) :
    ∃ r A : ℕ,
      ∀ N : ℕ, 2 ≤ N →
        (∀ t ∈ T,
          ¬ (g * (A + T.prod
            (fun u => Nat.nth Nat.Prime (r + u)) * N) + t).Prime) ∧
        (∀ t ∈ T, ∀ h ∈ H,
          ¬ Nat.nth Nat.Prime (r + t) ∣
            g * (A + T.prod
              (fun u => Nat.nth Nat.Prime (r + u)) * N) + h) := by
  obtain ⟨r, A, hdiv, hprotect, _hcomp⟩ :=
    bftb_exists_composite_crt_shift_from_bound
      hg hgB hT hH hdisj
  let q : ℕ → ℕ := fun t => Nat.nth Nat.Prime (r + t)
  have hqprime : ∀ t ∈ T, (q t).Prime := by
    intro t ht
    exact bftbAuxPrime_prime r t
  refine ⟨r, A, ?_⟩
  intro N hN
  constructor
  · simpa [q] using
      (bftb_crt_product_shift_forces_composite_of_two_le
        (T := T) (g := g) (A := A) (N := N)
        q hg hqprime hdiv hN)
  · simpa [q] using
      (bftb_crt_shift_product_preserves_protected
        (T := T) (H := H) (g := g) (A := A) (N := N)
        q hprotect)

end OmegaBalance
