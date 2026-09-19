import CanonicalRoots.TernaryEquationSemantics

noncomputable section
open CanonicalRoots

-- The actual display order synchronizes weights, exponent columns, and monomial-map rows.
example : (ternaryEquation 7 ⟨.V,2,3,5⟩).weights = [4,9,11] ∧
    (ternaryEquation 7 ⟨.V,2,3,5⟩).exponents = [[0,1,2],[1,3,0],[5,0,1]] ∧
    (ternaryEquation 7 ⟨.V,2,3,5⟩).monomialMatrix = [[0,1,2],[1,5,0],[3,0,1]] := by
  norm_num [ternaryEquation, candidateWeights, Cox.weights, List.finRange,
    List.mergeSort, List.merge, Cox.exponents, Cox.monomials]

-- Equal weights retain the actual stable sort order.
example : displayVariableOrder ![3,3,1] = [2,0,1] := by
  norm_num [displayVariableOrder, List.finRange, List.mergeSort, List.merge]

example {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    Nonempty (GradedAlgEquiv (ternaryEquation a e).piece
      (rootPiece (candidateTarget ha he).signature (candidateTarget ha he).tau)) :=
  ⟨ternaryEquationGradedEquiv ha he⟩

example : IsolatedAtOrigin (ternaryEquation 7 ⟨.V,2,3,5⟩).polynomial :=
  ternaryEquation_polynomial_isolated (by decide)

example {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    ∃ t : Target 3 a, t.signature = candidateSignature e ∧
      t.presentation.weights = (ternaryEquation a e).natWeights ∧
      (t.presentation.relationDegree : ℤ) = (ternaryEquation a e).relationDegree ∧
      t.presentation.polynomial = (ternaryEquation a e).polynomial :=
  ternaryEquation_realization ha he
