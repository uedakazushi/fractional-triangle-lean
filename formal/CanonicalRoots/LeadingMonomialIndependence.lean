import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace CanonicalRoots
open MvPolynomial
open scoped MonomialOrder

/-- Distinct leading monomials force linear independence, for any monomial order. -/
theorem linearIndependent_of_distinct_leading_monomials {σ ι K : Type*} [Field K]
    (m : MonomialOrder σ) (f : ι → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0) (hd : Function.Injective (fun i => m.degree (f i))) :
    LinearIndependent K f := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  by_contra hn
  let t := s.filter (fun j => c j ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi,hn⟩⟩
  obtain ⟨j,hj,hmax⟩ := t.exists_max_image (fun k => m.toSyn (m.degree (f k))) ht
  have hjc : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hz := congrArg (fun p : MvPolynomial σ K => p.coeff (m.degree (f j))) hc
  rw [coeff_sum] at hz
  have heq : ∑ k ∈ s, (c k • f k).coeff (m.degree (f j)) =
      c j * (f j).coeff (m.degree (f j)) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hks hkj
      by_cases hk : c k = 0
      · simp [hk]
      have hkt : k ∈ t := Finset.mem_filter.mpr ⟨hks,hk⟩
      have hlt : m.degree (f k) ≺[m] m.degree (f j) := by
        apply lt_of_le_of_ne (hmax k hkt)
        intro heq
        exact hkj (hd (m.toSyn.injective heq))
      simp [m.coeff_eq_zero_of_lt hlt]
    · exact fun h => (h hjs).elim
  rw [heq] at hz
  exact (mul_ne_zero hjc ((m.coeff_degree_ne_zero_iff).mpr (hf j))) (by simpa using hz)

end CanonicalRoots
