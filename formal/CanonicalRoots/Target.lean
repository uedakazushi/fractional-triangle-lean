import CanonicalRoots.Semantics

noncomputable section
namespace CanonicalRoots
open MvPolynomial

abbrev PresentedRing {n : ℕ} (f : MvPolynomial (Fin n) ℂ) :=
  MvPolynomial (Fin n) ℂ ⧸ Ideal.span {f}

def presentedPiece {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ) (m : ℕ) :
    Submodule ℂ (PresentedRing f) :=
  (weightedHomogeneousSubmodule ℂ w m).map (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})).toLinearMap

/-- An actual isolated homogeneous hypersurface presentation, independent of candidate data.
The cotangent-space interpretation and minimal generator bound are proved in
`PresentedCotangent` and `MinimalGenerators`. `HypersurfaceNumerics` derives the
numerical identity h = a + sum(weights) from the actual Hilbert series.
`CanonicalParameter` identifies the actual graded Ext canonical module with the corresponding shift. -/
structure RootHypersurfacePresentation {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) where
  weights : Fin n → ℕ
  weights_pos : ∀ i, 0 < weights i
  relationDegree : ℕ
  relationDegree_pos : 0 < relationDegree
  polynomial : MvPolynomial (Fin n) ℂ
  polynomial_ne_zero : polynomial ≠ 0
  homogeneous : IsWeightedHomogeneous weights polynomial relationDegree
  no_constant_or_linear : HasNoConstantOrLinear polynomial
  isolated : IsolatedAtOrigin polynomial
  graded_equiv : GradedAlgEquiv (presentedPiece polynomial weights) (rootPiece p τ)

/-- The proposed classification domain, with all signatures and actual roots quantified. -/
structure Target (n a : ℕ) where
  dimension_input : 3 ≤ n
  parameter_input : 1 ≤ a
  signature : Fin n → ℕ
  admissible : AdmissibleSignature signature
  tau : DegreeGroup signature
  root_equation : IsCanonicalRoot signature a tau
  presentation : RootHypersurfacePresentation signature tau

end CanonicalRoots
