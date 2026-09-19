import CanonicalRoots.PresentedCotangent
import CanonicalRoots.AugmentationCotangentEquiv
import CanonicalRoots.GradedEquivComposition

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem presentedAugmentation_eq_zero_of_positive_piece {n : ℕ}
    (f : MvPolynomial (Fin n) ℂ) (h0 : f.coeff 0 = 0) (w : Fin n → ℕ)
    (m : ℕ) (hm : 0 < m) (z : PresentedRing f) (hz : z ∈ presentedPiece f w m) :
    presentedAugmentation f h0 z = 0 := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hz
  change presentedAugmentation f h0 (Ideal.Quotient.mk (Ideal.span {f}) g) = 0
  rw [presentedAugmentation_mk]
  by_contra hn
  have he := hg hn
  simp only [map_zero] at he
  omega

/-- Positive source weights force any degree-preserving algebra equivalence to preserve the origin. -/
theorem presentedGradedEquiv_origin {n : ℕ} (f g : MvPolynomial (Fin n) ℂ)
    (hf : f.coeff 0 = 0) (hg : g.coeff 0 = 0) (w v : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (e : GradedAlgEquiv (presentedPiece f w) (presentedPiece g v)) :
    (presentedAugmentation g hg).comp e.toAlgEquiv.toAlgHom = presentedAugmentation f hf := by
  have hp : ((presentedAugmentation g hg).comp e.toAlgEquiv.toAlgHom).comp
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) =
      (presentedAugmentation f hf).comp (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) := by
    apply MvPolynomial.algHom_ext
    intro i
    change presentedAugmentation g hg (e.toAlgEquiv (Ideal.Quotient.mk (Ideal.span {f}) (X i))) =
      presentedAugmentation f hf (Ideal.Quotient.mk (Ideal.span {f}) (X i))
    rw [presentedAugmentation_mk, show (X i : MvPolynomial (Fin n) ℂ).coeff 0 = 0 from by simp]
    apply presentedAugmentation_eq_zero_of_positive_piece g hg v (w i) (hw i)
    apply (e.preserves (w i) _).mp
    exact Submodule.mem_map.mpr ⟨X i, isWeightedHomogeneous_X ℂ w i, rfl⟩
  apply AlgHom.ext
  intro z
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {f}) z
  exact AlgHom.congr_fun hp h

theorem presentedGradedEquiv_origin_ideal {n : ℕ} (f g : MvPolynomial (Fin n) ℂ)
    (hf : f.coeff 0 = 0) (hg : g.coeff 0 = 0) (w v : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (e : GradedAlgEquiv (presentedPiece f w) (presentedPiece g v)) :
    (presentedOriginIdeal f).map e.toAlgEquiv.toRingHom = presentedOriginIdeal g := by
  rw [presentedOriginIdeal_eq_ker f hf, presentedOriginIdeal_eq_ker g hg]
  exact augmentationKer_map_equiv _ _ e.toAlgEquiv (presentedGradedEquiv_origin f g hf hg w v hw e)

end CanonicalRoots
