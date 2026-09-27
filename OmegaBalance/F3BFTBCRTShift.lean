import OmegaBalance.F3BFTBAuxPrimes

namespace OmegaBalance

/-- A proper prime divisor certifies that the target natural number is composite. -/
theorem bftb_not_prime_of_prime_dvd_lt
    {q n : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hlt : q < n) :
    ¬ n.Prime := by
  intro hn
  rcases (Nat.dvd_prime hn).mp hqn with hq1 | hqn'
  · exact (ne_of_gt hq.one_lt) hq1
  · exact (ne_of_lt hlt) hqn'

/-- Package proper CRT divisors into compositeness of every excluded value. -/
theorem bftb_crt_divisors_force_composite
    {T : Finset ℕ} {g A : ℕ} (q : ℕ → ℕ)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hdiv : ∀ t ∈ T, q t ∣ g * A + t)
    (hlt : ∀ t ∈ T, q t < g * A + t) :
    ∀ t ∈ T, ¬ (g * A + t).Prime := by
  intro t ht
  exact bftb_not_prime_of_prime_dvd_lt
    (hqprime t ht) (hdiv t ht) (hlt t ht)

/-- Every assigned auxiliary modulus divides their finite product. -/
theorem bftb_crt_modulus_dvd_product
    {T : Finset ℕ} (q : ℕ → ℕ) {t : ℕ} (ht : t ∈ T) :
    q t ∣ T.prod q := by
  exact Finset.dvd_prod_of_mem q ht

/--
Adding a multiple of the product of all auxiliary moduli to a CRT representative
preserves every forced divisor.
-/
theorem bftb_crt_shift_product_preserves_divisors
    {T : Finset ℕ} {g A N : ℕ} (q : ℕ → ℕ)
    (hdiv : ∀ t ∈ T, q t ∣ g * A + t) :
    ∀ t ∈ T, q t ∣ g * (A + T.prod q * N) + t := by
  intro t ht
  have hqQ : q t ∣ T.prod q :=
    bftb_crt_modulus_dvd_product q ht
  have hqQN : q t ∣ T.prod q * N :=
    dvd_mul_of_dvd_left hqQ N
  have hqgQN : q t ∣ g * (T.prod q * N) :=
    dvd_mul_of_dvd_right hqQN g
  have hsum : q t ∣ (g * A + t) + g * (T.prod q * N) :=
    dvd_add (hdiv t ht) hqgQN
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

/--
The same product shift preserves every protected nondivisibility condition.
-/
theorem bftb_crt_shift_product_preserves_protected
    {T H : Finset ℕ} {g A N : ℕ} (q : ℕ → ℕ)
    (hprotect : ∀ t ∈ T, ∀ h ∈ H, ¬ q t ∣ g * A + h) :
    ∀ t ∈ T, ∀ h ∈ H,
      ¬ q t ∣ g * (A + T.prod q * N) + h := by
  intro t ht h hh hnew
  have hqQ : q t ∣ T.prod q :=
    bftb_crt_modulus_dvd_product q ht
  have hQzero : T.prod q ≡ 0 [MOD q t] :=
    Nat.modEq_zero_iff_dvd.mpr hqQ
  have hQNzero : T.prod q * N ≡ 0 [MOD q t] := by
    simpa using hQzero.mul_right N
  have hArep : A + T.prod q * N ≡ A [MOD q t] := by
    simpa using hQNzero.add_left A
  have hshift :
      g * (A + T.prod q * N) + h ≡ g * A + h [MOD q t] :=
    (hArep.mul_left g).add_right h
  have hnewzero : g * (A + T.prod q * N) + h ≡ 0 [MOD q t] :=
    Nat.modEq_zero_iff_dvd.mpr hnew
  have holdzero : g * A + h ≡ 0 [MOD q t] :=
    hshift.symm.trans hnewzero
  exact hprotect t ht h hh (Nat.modEq_zero_iff_dvd.mp holdzero)

/--
A concrete shift by twice the product makes every assigned auxiliary prime a
proper divisor of its excluded value.
-/
theorem bftb_crt_two_product_shift_proper
    {T : Finset ℕ} {g A : ℕ} (q : ℕ → ℕ)
    (hg : 0 < g)
    (hqprime : ∀ t ∈ T, (q t).Prime) :
    ∀ t ∈ T, q t < g * (A + T.prod q * 2) + t := by
  intro t ht
  have hQpos : 0 < T.prod q := by
    exact Finset.prod_pos (fun i hi => (hqprime i hi).pos)
  have hqQ : q t ∣ T.prod q :=
    bftb_crt_modulus_dvd_product q ht
  have hqleQ : q t ≤ T.prod q :=
    Nat.le_of_dvd hQpos hqQ
  have hQlt2Q : T.prod q < T.prod q * 2 := by
    omega
  have h2Qle : T.prod q * 2 ≤ A + T.prod q * 2 := by
    omega
  have hmul :
      A + T.prod q * 2 ≤ g * (A + T.prod q * 2) :=
    Nat.le_mul_of_pos_left _ hg
  have hadd :
      g * (A + T.prod q * 2) ≤ g * (A + T.prod q * 2) + t := by
    omega
  exact lt_of_lt_of_le
    (lt_of_le_of_lt hqleQ hQlt2Q)
    (h2Qle.trans (hmul.trans hadd))

/--
The explicit twice-product shift upgrades the finite CRT divisibility conditions
to actual compositeness of every excluded value.
-/
theorem bftb_crt_two_product_shift_forces_composite
    {T : Finset ℕ} {g A : ℕ} (q : ℕ → ℕ)
    (hg : 0 < g)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hdiv : ∀ t ∈ T, q t ∣ g * A + t) :
    ∀ t ∈ T, ¬ (g * (A + T.prod q * 2) + t).Prime := by
  apply bftb_crt_divisors_force_composite q hqprime
  · exact bftb_crt_shift_product_preserves_divisors (N := 2) q hdiv
  · exact bftb_crt_two_product_shift_proper q hg hqprime

end OmegaBalance
