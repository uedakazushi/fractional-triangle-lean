import CanonicalRoots.CanonicalParameter
import CanonicalRoots.OutputClassification

noncomputable section
open CanonicalRoots MvPolynomial
open scoped ModuleCat.Algebra

example {n a : ℕ} (t : Target n a) :
    HasCanonicalParameter t.presentation.polynomial t.presentation.polynomial_ne_zero
      t.presentation.weights t.presentation.relationDegree a := t.canonical_parameter

-- The grading statement includes all negative degrees, and is linear over the quotient itself.
example {n a : ℕ} (t : Target n a) :
    letI := principalExtQuotientModule t.presentation.polynomial t.presentation.polynomial_ne_zero
    ∃ e : PresentedRing t.presentation.polynomial ≃ₗ[PresentedRing t.presentation.polynomial]
        PrincipalExt t.presentation.polynomial,
      ∀ m : ℤ, ∀ x,
        e x ∈ hypersurfaceCanonicalPiece t.presentation.polynomial t.presentation.polynomial_ne_zero
          t.presentation.weights t.presentation.relationDegree m ↔
        x ∈ presentedIntegerPiece t.presentation.polynomial t.presentation.weights (m + a) :=
  t.canonical_parameter.2

example {n a : ℕ} (t : Target n a) :
    principalExtEquivOfAlgebra ℂ t.presentation.polynomial t.presentation.polynomial_ne_zero 1 ∈
      hypersurfaceCanonicalPiece t.presentation.polynomial t.presentation.polynomial_ne_zero
        t.presentation.weights t.presentation.relationDegree (-(a : ℤ)) := by
  rw [mem_hypersurfaceCanonicalPiece_iff]
  have hd : (t.presentation.relationDegree : ℤ) = (a : ℤ) + ∑ i, (t.presentation.weights i : ℤ) :=
    by exact_mod_cast t.relationDegree_eq_add_sum_weights
  rw [show (t.presentation.relationDegree : ℤ) + -(a : ℤ) -
    ∑ i, (t.presentation.weights i : ℤ) = 0 from by omega]
  exact ⟨1,isWeightedHomogeneous_one (R := ℂ) (fun i => (t.presentation.weights i : ℤ)),
    map_one (Ideal.Quotient.mkₐ ℂ (Ideal.span {t.presentation.polynomial}))⟩
