import OmegaBalance.F3PrimeDensityAPLimit

namespace OmegaBalance

lemma totient_pow_three (k : ℕ) (hk : 0 < k) :
    (3 ^ k).totient = 3 ^ (k - 1) * 2 := by
  simpa using (Nat.totient_prime_pow Nat.prime_three hk)

end OmegaBalance
