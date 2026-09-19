import CanonicalRoots.PrincipalExtScalars
import CanonicalRoots.ShiftedPolynomialHom

noncomputable section
namespace CanonicalRoots
open MvPolynomial
open scoped ModuleCat.Algebra

/-- Integer-indexed homogeneous pieces of the actual hypersurface quotient. -/
def presentedIntegerPiece {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ) (m : ℤ) :
    Submodule ℂ (PresentedRing f) :=
  (weightedHomogeneousSubmodule ℂ (fun i => (w i : ℤ)) m).map
    (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})).toLinearMap

theorem presentedIntegerPiece_nat {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (m : ℕ) : presentedIntegerPiece f w m = presentedPiece f w m := by
  unfold presentedIntegerPiece presentedPiece
  congr 1
  ext p
  exact isWeightedHomogeneous_int_iff w p m

/-- The canonical Ext grading from the dual of S(-h) → S with target S(-Σw).
Its definition uses degrees of homogeneous maps, before computing any shift of the quotient. -/
def hypersurfaceCanonicalPiece {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0)
    (w : Fin n → ℕ) (h : ℕ) (m : ℤ) : Submodule ℂ (PrincipalExt f) :=
  ((shiftedPolynomialHomPiece w h (∑ i, (w i : ℤ)) m).map
    (LinearMap.ringLmapEquivSelf (MvPolynomial (Fin n) ℂ) ℂ
      (MvPolynomial (Fin n) ℂ)).toLinearMap).map (principalBoundaryOfAlgebra ℂ f hf)

/-- The natural Ext¹ identification carries the dual-complex grading to the quotient shift. -/
theorem hypersurfaceCanonicalPiece_eq_map {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0)
    (w : Fin n → ℕ) (h : ℕ) (m : ℤ) :
    hypersurfaceCanonicalPiece f hf w h m =
      (presentedIntegerPiece f w ((h : ℤ) + m - ∑ i, (w i : ℤ))).map
        (principalExtEquivOfAlgebra ℂ f hf).toLinearMap := by
  rw [hypersurfaceCanonicalPiece, shiftedPolynomialHomPiece_map_eval]
  unfold presentedIntegerPiece
  rw [← Submodule.map_comp]
  congr 1

theorem mem_hypersurfaceCanonicalPiece_iff {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0)
    (w : Fin n → ℕ) (h : ℕ) (m : ℤ) (x : PresentedRing f) :
    principalExtEquivOfAlgebra ℂ f hf x ∈ hypersurfaceCanonicalPiece f hf w h m ↔
      x ∈ presentedIntegerPiece f w ((h : ℤ) + m - ∑ i, (w i : ℤ)) := by
  rw [hypersurfaceCanonicalPiece_eq_map]
  rw [Submodule.mem_map_equiv]
  simp

end CanonicalRoots
