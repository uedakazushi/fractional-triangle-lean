import CanonicalRoots.Semantics

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem ambient_monomial_fermat_relation {n : ℕ} (p : Fin n → ℕ) (t : Fin n →₀ ℕ) :
    ∑ i, ambientQuotient p (monomial (t + Finsupp.single i (p i)) 1) = 0 := by
  have hF : ambientQuotient p (fermat p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simp_rw [monomial_add_single, map_mul]
  rw [← Finset.mul_sum, ← map_sum]
  change ambientQuotient p (monomial t 1) * ambientQuotient p (fermat p) = 0
  rw [hF, mul_zero]

/-- Replacing one Fermat term preserves membership in any subalgebra containing the other terms. -/
theorem fermat_monomial_mem_of_other_terms {n : ℕ} (p : Fin n → ℕ)
    (S : Subalgebra ℂ (AmbientRing p)) (t : Fin n →₀ ℕ) (i : Fin n)
    (h : ∀ j, j ≠ i → ambientQuotient p (monomial (t + Finsupp.single j (p j)) 1) ∈ S) :
    ambientQuotient p (monomial (t + Finsupp.single i (p i)) 1) ∈ S := by
  classical
  have hsum : (∑ j ∈ Finset.univ.erase i,
      ambientQuotient p (monomial (t + Finsupp.single j (p j)) 1)) ∈ S := by
    apply S.sum_mem
    intro j hj
    exact h j (Finset.mem_erase.mp hj).1
  have heq : ambientQuotient p (monomial (t + Finsupp.single i (p i)) 1) =
      -(∑ j ∈ Finset.univ.erase i, ambientQuotient p (monomial (t + Finsupp.single j (p j)) 1)) := by
    apply eq_neg_of_add_eq_zero_left
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact ambient_monomial_fermat_relation p t
  rw [heq]
  exact S.neg_mem hsum

end CanonicalRoots
