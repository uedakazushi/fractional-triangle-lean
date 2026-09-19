import CanonicalRoots.PointCompletedLocalAction
import CanonicalRoots.RootDimension
import Mathlib.RingTheory.AdicCompletion.LocalRing

noncomputable section
namespace CanonicalRoots
open IsLocalRing

/-- A ring equivalence from an actual local completion preserves the original embedding dimension. -/
theorem localCompletion_embeddingDim_equiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S]
    (e : AdicCompletion (maximalIdeal R) R ≃+* S) :
    (maximalIdeal S).spanFinrank = (maximalIdeal R).spanFinrank := by
  rw [← map_ringEquiv_maximalIdeal e, Ideal.spanFinrank_map_eq_of_ringEquiv,
    AdicCompletion.spanFinrank_maximalIdeal_eq]

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
  (z : AmbientRing p →ₐ[ℂ] ℂ)

include hp ha hτ in
/-- The stabilizer fixed algebra of the completed actual local ring is itself local. -/
theorem pointCompletedLocalFixed_isLocalRing : IsLocalRing (pointCompletedLocalFixed p τ z) := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  exact (rootLocalPointCompletedInvariantEquiv p τ z hp ha hτ).isLocalRing

include hp ha hτ in
/-- The completed invariant model measures the cotangent dimension of the original root local ring. -/
theorem rootPointCompleted_embeddingDim :
    letI := pointCompletedLocalFixed_isLocalRing p τ hp ha hτ z
    (maximalIdeal (pointCompletedLocalFixed p τ z)).spanFinrank =
      Module.finrank (ResidueField (AugmentationLocalRing (rootPoint p τ z)))
        (CotangentSpace (AugmentationLocalRing (rootPoint p τ z))) := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  let : IsLocalRing (pointCompletedLocalFixed p τ z) := pointCompletedLocalFixed_isLocalRing p τ hp ha hτ z
  rw [localCompletion_embeddingDim_equiv (rootLocalPointCompletedInvariantEquiv p τ z hp ha hτ),
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]

include hp ha hτ in
/-- Every original root point has local Krull dimension at most the proved global dimension. -/
theorem rootPointLocal_krullDim_le : ringKrullDim (AugmentationLocalRing (rootPoint p τ z)) ≤ n := by
  rw [← canonicalRoot_krullDim p hp ha τ hτ]
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker (rootPoint p τ z).toRingHom)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

end CanonicalRoots
