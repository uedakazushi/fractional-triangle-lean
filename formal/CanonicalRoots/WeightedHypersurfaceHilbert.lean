import CanonicalRoots.WeightedPolynomialHilbert
import CanonicalRoots.PrimitiveWeights

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def presentedHilbertSeries {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun m => (Module.finrank ℂ (presentedPiece f w m) : ℚ))

/-- The standard hypersurface Hilbert formula follows from actual degree-wise rank-nullity. -/
theorem presentedHilbertSeries_eq {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (h : ℕ)
    (hf : IsWeightedHomogeneous w f h) (hne : f ≠ 0) :
    presentedHilbertSeries f w = (1 - PowerSeries.X ^ h) * weightedPolynomialHilbertSeries w := by
  have he : presentedHilbertSeries f w + PowerSeries.X ^ h * weightedPolynomialHilbertSeries w =
      weightedPolynomialHilbertSeries w := by
    apply PowerSeries.ext
    intro m
    simp only [map_add, presentedHilbertSeries, weightedPolynomialHilbertSeries,
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    have hd := presentedPiece_finrank_add f w hw h hf hne m
    split_ifs at hd ⊢ with hm <;> exact_mod_cast hd
  linear_combination he

theorem presentedHilbertSeries_mul_denominator {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (h : ℕ)
    (hf : IsWeightedHomogeneous w f h) (hne : f ≠ 0) :
    presentedHilbertSeries f w * ∏ i, (1 - PowerSeries.X ^ w i) = 1 - PowerSeries.X ^ h := by
  rw [presentedHilbertSeries_eq f w hw h hf hne, mul_assoc,
    weightedPolynomialHilbertSeries_mul_denominator w hw, mul_one]

namespace GradedAlgEquiv

/-- A graded algebra equivalence restricts to an actual linear equivalence in each degree. -/
def pieceEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    {s : ℕ → Submodule ℂ A} {t : ℕ → Submodule ℂ B} (e : GradedAlgEquiv s t) (m : ℕ) :
    s m ≃ₗ[ℂ] t m where
  toFun x := ⟨e.toAlgEquiv x, (e.preserves m x).mp x.property⟩
  invFun y := ⟨e.toAlgEquiv.symm y, (e.preserves m _).mpr (by simpa using y.property)⟩
  left_inv _ := by apply Subtype.ext; exact e.toAlgEquiv.symm_apply_apply _
  right_inv _ := by apply Subtype.ext; exact e.toAlgEquiv.apply_symm_apply _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

end GradedAlgEquiv

namespace RootHypersurfacePresentation

theorem hilbertSeries_eq {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (P : RootHypersurfacePresentation p τ) :
    presentedHilbertSeries P.polynomial P.weights = rootHilbertSeries p τ := by
  apply PowerSeries.ext
  intro m
  simp only [presentedHilbertSeries, rootHilbertSeries, PowerSeries.coeff_mk]
  exact_mod_cast (P.graded_equiv.pieceEquiv m).finrank_eq

theorem hilbertSeries_mul_denominator {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (P : RootHypersurfacePresentation p τ) :
    rootHilbertSeries p τ * ∏ i, (1 - PowerSeries.X ^ P.weights i) =
      1 - PowerSeries.X ^ P.relationDegree := by
  rw [← P.hilbertSeries_eq p τ]
  exact presentedHilbertSeries_mul_denominator _ _ P.weights_pos _ P.homogeneous P.polynomial_ne_zero

end RootHypersurfacePresentation
end CanonicalRoots
