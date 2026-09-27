import OmegaBalance.F3BFTBPigeonhole

namespace OmegaBalance

/--
Convert an indexed finite tuple into the local finset many-primes interface.
This is the combinatorial adapter needed to reuse an upstream Maynard--Tao
statement whose tuple is presented as `Fin k → ℕ`.
-/
theorem bftb_indexed_many_primes_to_finset
    {k m : ℕ} (h : Fin k → ℕ) (hinj : Function.Injective h)
    (hmany :
      ({n : ℕ |
        m ≤ (Finset.univ.filter fun i : Fin k => (n + h i).Prime).card} : Set ℕ).Infinite) :
    (BFTBAtLeastPrimeCountSet
      (fun n t => n + t) (Finset.image h Finset.univ) m).Infinite := by
  have heq :
      ({n : ℕ |
        m ≤ (Finset.univ.filter fun i : Fin k => (n + h i).Prime).card} : Set ℕ) =
      BFTBAtLeastPrimeCountSet
        (fun n t => n + t) (Finset.image h Finset.univ) m := by
    ext n
    simp only [BFTBAtLeastPrimeCountSet, Set.mem_setOf_eq]
    rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
  rw [← heq]
  exact hmany

end OmegaBalance
