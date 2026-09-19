import CanonicalRoots.CoxFermatRealization
import CanonicalRoots.MonicPresentedBasis

noncomputable section
open CanonicalRoots MvPolynomial

-- Both index one and index five are realized by actual isolated root hypersurfaces.
example : ∃ t : Target 3 1, t.signature = candidateSignature ⟨.I,2,3,7⟩ ∧
    (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.I,2,3,7⟩ i) ∧
    (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.I,2,3,7⟩ ∧
    t.presentation.polynomial = candidateRelation ⟨.I,2,3,7⟩ :=
  fermat_candidate_realization (by decide) (by decide)

example : ∃ t : Target 3 5, t.signature = candidateSignature ⟨.I,2,3,11⟩ ∧
    (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.I,2,3,11⟩ i) ∧
    (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.I,2,3,11⟩ ∧
    t.presentation.polynomial = candidateRelation ⟨.I,2,3,11⟩ :=
  fermat_candidate_realization (by decide) (by decide)

-- Common factors are rejected by the independent arithmetic predicate.
example : ¬ ArithmeticTernary 1 ⟨.I,2,4,5⟩ := by decide

-- The general monic basis works for mixed terms, not only Fermat equations.
example : LinearIndependent ℂ
    (separatedMonomialBasis 5 (by decide) (X (0 : Fin 2) ^ 3 * X 1 + X 1 ^ 4)) :=
  Module.Basis.linearIndependent _

example {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    HasNoConstantOrLinear (candidateRelation e) ∧ candidateRelation e ≠ 0 :=
  ⟨candidateRelation_no_constant_or_linear ha he, candidateRelation_ne_zero e⟩
