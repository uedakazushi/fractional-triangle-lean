import CanonicalRoots.AugmentationCotangentEquiv
import CanonicalRoots.RootPresentationOrigin
import CanonicalRoots.PresentedCotangent

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
  (H : RootHypersurfacePresentation p τ)

include hp ha hτ in
theorem RootHypersurfacePresentation.origin_preserved :
    (rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ).comp
      H.graded_equiv.toAlgEquiv.toAlgHom = presentedAugmentation H.polynomial H.no_constant_or_linear.1 := by
  apply AlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {H.polynomial}) x
  exact AlgHom.congr_fun (H.polynomialMap_origin p τ hp ha hτ) f

/-- The original root origin has the cotangent space specified by its actual minimal presentation. -/
def RootHypersurfacePresentation.rootOriginCotangentEquiv :
    (RingHom.ker (rootOriginPoint p
      (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ).toRingHom).Cotangent ≃ₗ[ℂ] (Fin n → ℂ) := by
  let E : (RingHom.ker (presentedAugmentation H.polynomial H.no_constant_or_linear.1).toRingHom).Cotangent
      ≃ₗ[ℂ] (Fin n → ℂ) := by
    rw [← presentedOriginIdeal_eq_ker H.polynomial H.no_constant_or_linear.1]
    exact presentedOriginCotangentEquiv H.polynomial H.no_constant_or_linear
  exact (augmentationCotangentEquiv (presentedAugmentation H.polynomial H.no_constant_or_linear.1)
    (rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ)
    H.graded_equiv.toAlgEquiv (H.origin_preserved p τ hp ha hτ)).symm.trans E

include hp ha hτ H in
theorem RootHypersurfacePresentation.rootOriginCotangent_finrank :
    Module.finrank ℂ (RingHom.ker (rootOriginPoint p
      (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ).toRingHom).Cotangent = n := by
  exact (H.rootOriginCotangentEquiv p τ hp ha hτ).finrank_eq.trans (by simp)

end CanonicalRoots
