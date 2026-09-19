import CanonicalRoots.CoxMonicRealization

noncomputable section
open CanonicalRoots MvPolynomial

-- Type II: a nontrivial root index and non-coprime signature entries.
example : ArithmeticTernary 7 ⟨.II,3,3,4⟩ := by decide
example : candidateSignature ⟨.II,3,3,4⟩ = ![3,8,4] := by decide
example : ∃ t : Target 3 7, t.signature = candidateSignature ⟨.II,3,3,4⟩ ∧
    (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.II,3,3,4⟩ i) ∧
    (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.II,3,3,4⟩ ∧
    t.presentation.polynomial = candidateRelation ⟨.II,3,3,4⟩ :=
  monic_candidate_realization (by decide) (by decide) (Or.inl rfl)

-- Type III: all signature entries share a factor; the construction retains torsion.
example : ArithmeticTernary 19 ⟨.III,3,4,5⟩ := by decide
example : candidateSignature ⟨.III,3,4,5⟩ = ![10,15,5] := by decide
example : ∃ t : Target 3 19, t.signature = candidateSignature ⟨.III,3,4,5⟩ ∧
    (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.III,3,4,5⟩ i) ∧
    (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.III,3,4,5⟩ ∧
    t.presentation.polynomial = candidateRelation ⟨.III,3,4,5⟩ :=
  monic_candidate_realization (by decide) (by decide) (Or.inr rfl)

-- Isolation is proved for IV and V as well, independently of their remaining ring-isomorphism step.
example : IsolatedAtOrigin (candidateRelation ⟨.IV,3,4,2⟩) :=
  candidateRelation_isolated (a := 2) (by decide)
example : IsolatedAtOrigin (candidateRelation ⟨.V,2,3,5⟩) :=
  candidateRelation_isolated (a := 7) (by decide)

example : candidateExponentMap ⟨.III,3,4,5⟩ (Finsupp.equivFunOnFinite.symm ![2,1,1]) =
    Finsupp.equivFunOnFinite.symm ![11,6,1] := by
  ext i
  fin_cases i <;> simp [candidateExponentMap, candidateMonomialExponent, Cox.monomials, Fin.sum_univ_three]

example {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (hk : e.kind = .II ∨ e.kind = .III) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (i : Fin 3) :
    candidateMonicAlgEquiv ha he hk τ hτ
      ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) (X i)) =
        candidateRootGenerator ha he τ hτ i := by
  calc
    _ = candidateQuotientMap ha he τ hτ
        ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) (X i)) :=
      AlgEquiv.ofBijective_apply _ _ _
    _ = candidateRootGenerator ha he τ hτ i := by
      rw [candidateQuotientMap_mk, candidatePolynomialMap_X]
