import CanonicalRoots.BoundedMonomialBasis
import CanonicalRoots.AmbientPieceBasis

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem ambientPermutedBoundedBasis_homogeneous {n : ℕ} (p : Fin (n + 1) → ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (hp : 0 < p (e 0))
    (d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < p (e 0)}) :
    ambientPermutedBoundedBasis p e hp d ∈ ambientPiece p (Finsupp.weight (xDegree p) d.val) := by
  rw [ambientPermutedBoundedBasis_apply]
  exact Submodule.mem_map.mpr ⟨_, isWeightedHomogeneous_monomial _ _ _ rfl, rfl⟩

/-- Bounded root-degree monomials span the actual root module after eliminating any coordinate. -/
theorem rootModule_le_of_permuted_monomials {n : ℕ} (p : Fin (n + 1) → ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (hp : 0 < p (e 0)) (τ : DegreeGroup p)
    (S : Submodule ℂ (AmbientRing p))
    (hS : ∀ d : Fin (n + 1) →₀ ℕ, d (e 0) < p (e 0) →
      (∃ m : ℕ, Finsupp.weight (xDegree p) d = m • τ) →
      ambientQuotient p (monomial d 1) ∈ S) : rootModule p τ ≤ S := by
  classical
  apply iSup_le
  intro m x hx
  let b := ambientPermutedBoundedBasis p e hp
  have hrepr := b.linearCombination_repr x
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
  have hproject := congrArg (ambientProjection p (m • τ)) hrepr
  rw [ambientProjection_eq_self p (m • τ) hx, map_sum] at hproject
  rw [← hproject]
  apply Submodule.sum_mem
  intro d hd
  rw [map_smul, ambientProjection_of_mem p (m • τ) _
    (ambientPermutedBoundedBasis_homogeneous p e hp d)]
  split_ifs with h
  · apply S.smul_mem
    rw [ambientPermutedBoundedBasis_apply]
    exact hS d.val d.property ⟨m,h.symm⟩
  · simp

theorem rootMap_surjective_of_permuted_monomials {n : ℕ} (p : Fin (n + 1) → ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (hp : 0 < p (e 0)) (τ : DegreeGroup p)
    {A : Type*} [CommRing A] [Algebra ℂ A] (f : A →ₐ[ℂ] RootRing p τ)
    (hf : ∀ d : Fin (n + 1) →₀ ℕ, d (e 0) < p (e 0) →
      (∃ m : ℕ, Finsupp.weight (xDegree p) d = m • τ) →
      ∃ x : A, (f x : AmbientRing p) = ambientQuotient p (monomial d 1)) :
    Function.Surjective f := by
  have hs : rootModule p τ ≤ LinearMap.range ((rootSubalgebra p τ).val.toLinearMap.comp f.toLinearMap) :=
    rootModule_le_of_permuted_monomials p e hp τ _ hf
  intro y
  obtain ⟨x,hx⟩ := hs y.property
  exact ⟨x,Subtype.ext hx⟩

end CanonicalRoots
