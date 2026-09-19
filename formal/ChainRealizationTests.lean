import CanonicalRoots.ChainRealization

noncomputable section
open CanonicalRoots MvPolynomial

example : ∃ t : Target 3 2, t.signature = candidateSignature ⟨.IV,3,4,2⟩ ∧
    (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.IV,3,4,2⟩ i) ∧
    (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.IV,3,4,2⟩ ∧
    t.presentation.polynomial = candidateRelation ⟨.IV,3,4,2⟩ :=
  chain_candidate_realization (by decide) (by decide)

example : ArithmeticTernary 5 ⟨.IV,2,3,5⟩ := by decide
example : ∃ t : Target 3 5, t.signature = candidateSignature ⟨.IV,2,3,5⟩ ∧
    (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.IV,2,3,5⟩ i) ∧
    (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.IV,2,3,5⟩ ∧
    t.presentation.polynomial = candidateRelation ⟨.IV,2,3,5⟩ :=
  chain_candidate_realization (by decide) (by decide)

-- These monomials require repeated reduction by the ambient Fermat relation.
example : MonomialOrder.lex.degree
    (chainReducedMonomial 3 4 2 (Finsupp.equivFunOnFinite.symm ![7,2,1])) =
      Finsupp.equivFunOnFinite.symm ![16,5,1] := by
  rw [chainReducedMonomial_degree (by decide) (by decide)]
  ext i
  fin_cases i <;> norm_num [chainLeadingExponent]

example : MonomialOrder.lex.degree
    (chainReducedMonomial 2 3 5 (Finsupp.equivFunOnFinite.symm ![9,4,3])) =
      Finsupp.equivFunOnFinite.symm ![47,23,1] := by
  rw [chainReducedMonomial_degree (by decide) (by decide)]
  ext i
  fin_cases i <;> norm_num [chainLeadingExponent]

example {a α β γ : ℕ} (ha : 1 ≤ a) (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) (i : Fin 3) :
    candidateChainAlgEquiv ha he τ hτ
      ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.IV,α,β,γ⟩})) (X i)) =
        candidateRootGenerator ha he τ hτ i := by
  calc
    _ = candidateQuotientMap ha he τ hτ
        ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.IV,α,β,γ⟩})) (X i)) :=
      AlgEquiv.ofBijective_apply _ _ _
    _ = candidateRootGenerator ha he τ hτ i := by
      rw [candidateQuotientMap_mk, candidatePolynomialMap_X]
