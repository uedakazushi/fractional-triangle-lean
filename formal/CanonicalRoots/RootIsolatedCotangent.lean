import CanonicalRoots.CotangentJacobianBound
import CanonicalRoots.RootPresentationOrigin

noncomputable section
namespace CanonicalRoots
open MvPolynomial IsLocalRing

variable {n a : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
/-- The actual isolated presentation forces fewer than n cotangent directions
at every complex point other than the original graded root origin. -/
theorem RootHypersurfacePresentation.nonorigin_cotangent_lt
    (H : RootHypersurfacePresentation p τ) (ε : RootRing p τ →ₐ[ℂ] ℂ)
    (hε : ε ≠ rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ) :
    Module.finrank ℂ (RingHom.ker ε.toRingHom).Cotangent < n := by
  let q := H.polynomialMap p τ
  let v : Fin n → ℂ := fun i => ε (q (X i))
  have heval : ε.comp q = polynomialPoint v := by
    apply MvPolynomial.algHom_ext
    intro i
    exact (aeval_X v i).symm
  have hv : v ≠ 0 := by
    intro hzero
    apply hε
    have he : ε.comp q = (rootOriginPoint p
        (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ).comp q := by
      rw [H.polynomialMap_origin p τ hp ha hτ, heval, hzero]
      rfl
    apply AlgHom.ext
    intro r
    obtain ⟨g, rfl⟩ := H.polynomialMap_surjective p τ r
    exact AlgHom.congr_fun he g
  have hderiv : ∃ i, eval v (pderiv i H.polynomial) ≠ 0 := by
    by_contra! h
    exact hv ((H.isolated v).mp h)
  obtain ⟨i, hi⟩ := hderiv
  exact cotangent_finrank_lt_of_derivative ε q (H.polynomialMap_surjective p τ) v heval
    H.polynomial (H.polynomialMap_relation p τ) i hi

include hp ha hτ in
theorem RootHypersurfacePresentation.nonorigin_local_cotangent_lt
    (H : RootHypersurfacePresentation p τ) (ε : RootRing p τ →ₐ[ℂ] ℂ)
    (hε : ε ≠ rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ) :
    Module.finrank (ResidueField (AugmentationLocalRing ε))
      (CotangentSpace (AugmentationLocalRing ε)) < n := by
  rw [augmentationLocalCotangent_finrank]
  exact H.nonorigin_cotangent_lt p τ hp ha hτ ε hε

end CanonicalRoots
