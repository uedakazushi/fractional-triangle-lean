import CanonicalRoots.RootReindex
import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin n → ℕ) (e : Equiv.Perm (Fin n)) (τ : DegreeGroup p)

/-- The same isolated presentation describes the coordinate-permuted actual root ring. -/
def RootHypersurfacePresentation.reindex (H : RootHypersurfacePresentation p τ) :
    RootHypersurfacePresentation (fun i => p (e i)) ((degreeReindex p e).symm τ) where
  weights := H.weights
  weights_pos := H.weights_pos
  relationDegree := H.relationDegree
  relationDegree_pos := H.relationDegree_pos
  polynomial := H.polynomial
  polynomial_ne_zero := H.polynomial_ne_zero
  homogeneous := H.homogeneous
  no_constant_or_linear := H.no_constant_or_linear
  isolated := H.isolated
  graded_equiv := {
    toAlgEquiv := H.graded_equiv.toAlgEquiv.trans (rootReindex p e τ).symm
    preserves := by
      intro m x
      have h := rootReindex_preserves p e τ m ((rootReindex p e τ).symm (H.graded_equiv.toAlgEquiv x))
      rw [AlgEquiv.apply_symm_apply] at h
      exact (H.graded_equiv.preserves m x).trans h.symm }

def Target.reindex {a : ℕ} (t : Target n a) (e : Equiv.Perm (Fin n)) : Target n a where
  dimension_input := t.dimension_input
  parameter_input := t.parameter_input
  signature := fun i => t.signature (e i)
  admissible := admissibleSignature_reindex t.signature e t.admissible
  tau := (degreeReindex t.signature e).symm t.tau
  root_equation := canonicalRoot_reindex t.signature e t.tau t.root_equation
  presentation := t.presentation.reindex t.signature e t.tau

end CanonicalRoots
