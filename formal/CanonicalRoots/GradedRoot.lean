import CanonicalRoots.RootExample
import CanonicalRoots.RationalDegree
import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem monomial_weight_root {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (w : Fin n → ℕ) (hw : ∀ i, xDegree p i = w i • τ) (d : Fin n →₀ ℕ) :
    Finsupp.weight (xDegree p) d = Finsupp.weight w d • τ := by
  simp only [Finsupp.weight_eq_sum, hw, smul_smul, smul_eq_mul, Finset.sum_smul]

/-- The actual group grading agrees with the proposed natural grading in every degree. -/
theorem homogeneous_root_iff {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (w : Fin n → ℕ) (hw : ∀ i, xDegree p i = w i • τ)
    (hinj : Function.Injective (fun m : ℕ => m • τ))
    (f : MvPolynomial (Fin n) ℂ) (m : ℕ) :
    IsWeightedHomogeneous (xDegree p) f (m • τ) ↔ IsWeightedHomogeneous w f m := by
  constructor
  · intro h d hd
    apply hinj
    change Finsupp.weight w d • τ = m • τ
    rw [← monomial_weight_root p τ w hw]
    exact h hd
  · intro h d hd
    rw [monomial_weight_root p τ w hw, h hd]

theorem ambientPiece_eq_presentedPiece {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (w : Fin n → ℕ) (hw : ∀ i, xDegree p i = w i • τ)
    (hinj : Function.Injective (fun m : ℕ => m • τ)) (m : ℕ) :
    ambientPiece p (m • τ) = presentedPiece (fermat p) w m := by
  have hs : weightedHomogeneousSubmodule ℂ (xDegree p) (m • τ) =
      weightedHomogeneousSubmodule ℂ w m := by
    ext f
    exact homogeneous_root_iff p τ w hw hinj f m
  unfold ambientPiece presentedPiece
  rw [hs]
  rfl

/-- A genuine graded algebra equivalence, strengthening the ungraded R=T criterion. -/
def rootGradedAmbientEquiv {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (w : Fin n → ℕ) (hw : ∀ i, xDegree p i = w i • τ)
    (hinj : Function.Injective (fun m : ℕ => m • τ)) :
    GradedAlgEquiv (rootPiece p τ) (presentedPiece (fermat p) w) where
  toAlgEquiv := rootAmbientEquiv p τ w hw
  preserves m x := by
    change (x : AmbientRing p) ∈ ambientPiece p (m • τ) ↔
      (x : AmbientRing p) ∈ presentedPiece (fermat p) w m
    rw [ambientPiece_eq_presentedPiece p τ w hw hinj]
    rfl

def example_root_graded_equiv :
    GradedAlgEquiv (rootPiece exampleSignature (omegaDegree exampleSignature))
      (presentedPiece (fermat exampleSignature) exampleWeights) :=
  rootGradedAmbientEquiv _ _ _ example_generator_degrees
    (root_multiples_injective _ example_signature_admissible (by decide) _ example_is_canonical_root)

end CanonicalRoots
