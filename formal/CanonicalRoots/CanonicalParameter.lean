import CanonicalRoots.HypersurfaceCanonicalGrading
import CanonicalRoots.PrincipalExtQuotient
import CanonicalRoots.HypersurfaceNumerics

noncomputable section
namespace CanonicalRoots
open MvPolynomial
open scoped ModuleCat.Algebra

/-- The canonical module Ext¹_S(S/(f), S(-Σw)) is the graded free module (S/(f))(a).
The quotient action is proved to descend the original polynomial-ring action. -/
def HasCanonicalParameter {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0)
    (w : Fin n → ℕ) (h a : ℕ) : Prop :=
  IsWeightedHomogeneous w f h ∧
  letI := principalExtQuotientModule f hf
  ∃ e : PresentedRing f ≃ₗ[PresentedRing f] PrincipalExt f,
    ∀ m : ℤ, ∀ x : PresentedRing f,
      e x ∈ hypersurfaceCanonicalPiece f hf w h m ↔ x ∈ presentedIntegerPiece f w (m + a)

theorem hasCanonicalParameter_of_degree {n h a : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0)
    (w : Fin n → ℕ) (hhom : IsWeightedHomogeneous w f h)
    (hd : h = a + ∑ i, w i) : HasCanonicalParameter f hf w h a := by
  refine ⟨hhom,?_⟩
  letI := principalExtQuotientModule f hf
  refine ⟨principalExtQuotientEquiv f hf,?_⟩
  intro m x
  have he : (h : ℤ) + m - ∑ i, (w i : ℤ) = m + a := by
    have hh : (h : ℤ) = (a : ℤ) + ∑ i, (w i : ℤ) := by exact_mod_cast hd
    omega
  change principalExtEquivOfAlgebra ℂ f hf x ∈ hypersurfaceCanonicalPiece f hf w h m ↔ _
  rw [mem_hypersurfaceCanonicalPiece_iff, he]

/-- Every independent actual target has the required canonical-module shift. -/
theorem Target.canonical_parameter {n a : ℕ} (t : Target n a) :
    HasCanonicalParameter t.presentation.polynomial t.presentation.polynomial_ne_zero
      t.presentation.weights t.presentation.relationDegree a :=
  hasCanonicalParameter_of_degree _ _ _ t.presentation.homogeneous t.relationDegree_eq_add_sum_weights

theorem Target.canonical_piece_nat {n a : ℕ} (t : Target n a) (m : ℕ)
    (x : PresentedRing t.presentation.polynomial) :
    principalExtEquivOfAlgebra ℂ t.presentation.polynomial t.presentation.polynomial_ne_zero x ∈
      hypersurfaceCanonicalPiece t.presentation.polynomial t.presentation.polynomial_ne_zero
        t.presentation.weights t.presentation.relationDegree (m : ℤ) ↔
      x ∈ presentedPiece t.presentation.polynomial t.presentation.weights (m + a) := by
  rw [mem_hypersurfaceCanonicalPiece_iff]
  have he : (t.presentation.relationDegree : ℤ) + m - ∑ i, (t.presentation.weights i : ℤ) =
      ((m + a : ℕ) : ℤ) := by
    have hd : (t.presentation.relationDegree : ℤ) = (a : ℤ) + ∑ i, (t.presentation.weights i : ℤ) :=
      by exact_mod_cast t.relationDegree_eq_add_sum_weights
    omega
  rw [he, presentedIntegerPiece_nat]

end CanonicalRoots
