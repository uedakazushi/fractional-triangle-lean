import CanonicalRoots.HigherEquationArity

noncomputable section
open CanonicalRoots

example : IsolatedAtOrigin (higherEquation 1 [2,3,7,43]).polynomial :=
  higherEquation_polynomial_isolated 1 _ (by decide)

example : Nonempty (GradedAlgEquiv
    (presentedPiece (fermat ![2,3,7,43]) (productWeights ![2,3,7,43]))
    (higherEquation 1 (List.ofFn ![2,3,7,43])).piece) :=
  ⟨higherEquationOfFnModelEquiv 1 _ (by decide)⟩

example {n : ℕ} (a : ℕ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) :
    Nonempty (GradedAlgEquiv (presentedPiece (fermat p) (productWeights p))
      (higherEquation a (List.ofFn p)).piece) :=
  ⟨higherEquationOfFnModelEquiv a p hp⟩
