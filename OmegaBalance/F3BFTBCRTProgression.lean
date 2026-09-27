import OmegaBalance.F3BFTBCRTComposite

namespace OmegaBalance

theorem bftb_crt_product_shift_proper_of_two_le
    {T : Finset ℕ} {g A N : ℕ} (q : ℕ → ℕ)
    (hg : 0 < g)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hN : 2 ≤ N) :
    ∀ t ∈ T, q t < g * (A + T.prod q * N) + t := by
  intro t ht
  have hQpos : 0 < T.prod q := by
    exact Finset.prod_pos (fun i hi => (hqprime i hi).pos)
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
      g * (A + T.prod q * N) ≤ g * (A + T.prod q * N) + t := by
    omega
  exact lt_of_lt_of_le
    (lt_of_le_of_lt hqleQ hQlt2Q)
    (h2QleQN.trans (hQNle.trans (hmul.trans hadd)))

theorem bftb_crt_product_shift_forces_composite_of_two_le
    {T : Finset ℕ} {g A N : ℕ} (q : ℕ → ℕ)
    (hg : 0 < g)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hdiv : ∀ t ∈ T, q t ∣ g * A + t)
    (hN : 2 ≤ N) :
    ∀ t ∈ T, ¬ (g * (A + T.prod q * N) + t).Prime := by
  apply bftb_crt_divisors_force_composite q hqprime
  · exact bftb_crt_shift_product_preserves_divisors (N := N) q hdiv
  · exact bftb_crt_product_shift_proper_of_two_le q hg hqprime hN

theorem bftb_crt_product_progression_rewrite
    {T : Finset ℕ} {g A n t : ℕ} (q : ℕ → ℕ) :
    g * (A + T.prod q * (n + 2)) + t =
      (g * T.prod q) * n + (g * (A + T.prod q * 2) + t) := by
  ring

theorem bftb_crt_linear_progression_forces_composite
    {T : Finset ℕ} {g A : ℕ} (q : ℕ → ℕ)
    (hg : 0 < g)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hdiv : ∀ t ∈ T, q t ∣ g * A + t) :
    ∀ n : ℕ, ∀ t ∈ T,
      ¬ ((g * T.prod q) * n + (g * (A + T.prod q * 2) + t)).Prime := by
  intro n t ht
  rw [← bftb_crt_product_progression_rewrite q]
  exact bftb_crt_product_shift_forces_composite_of_two_le
    q hg hqprime hdiv (by omega) t ht

end OmegaBalance
