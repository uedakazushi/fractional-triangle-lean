import CanonicalRoots.LoopRealization

noncomputable section
open CanonicalRoots MvPolynomial

-- The equation is a domain uniformly, independently of the arithmetic candidate predicate.
example (α β γ : ℕ) (hβ : 1 ≤ β) (hγ : 2 ≤ γ) :
    IsDomain (PresentedRing (candidateRelation ⟨.V,α,β,γ⟩)) :=
  loopPresentedRing_isDomain α β γ hβ hγ

example : ∃ t : Target 3 7, t.signature = candidateSignature ⟨.V,2,3,5⟩ ∧
    (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.V,2,3,5⟩ i) ∧
    (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.V,2,3,5⟩ ∧
    t.presentation.polynomial = candidateRelation ⟨.V,2,3,5⟩ :=
  loop_candidate_realization (by decide) (by decide)

example {a α β γ : ℕ} (ha : 1 ≤ a) (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) (i : Fin 3) :
    candidateLoopAlgEquiv ha he τ hτ
      ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.V,α,β,γ⟩})) (X i)) =
        candidateRootGenerator ha he τ hτ i := by
  calc
    _ = candidateQuotientMap ha he τ hτ
        ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.V,α,β,γ⟩})) (X i)) :=
      AlgEquiv.ofBijective_apply _ _ _
    _ = candidateRootGenerator ha he τ hτ i := by
      rw [candidateQuotientMap_mk, candidatePolynomialMap_X]
