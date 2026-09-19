import CanonicalRoots.RootLocalPointInvariant
import CanonicalRoots.AdicAutomorphismAction

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (z : AmbientRing p →ₐ[ℂ] ℂ)

/-- The original point stabilizer acts by automorphisms on the actual completed local ring. -/
def pointCompletedLocalCharacterAction :
    rootPointStabilizer p τ z →*
      (AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z)
        ≃ₐ[ℂ]
      AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z)) :=
  adicIdealAction _ (pointLocalCharacterAction p τ z)
    (fun χ => (IsLocalRing.map_ringEquiv_maximalIdeal
      (pointLocalCharacterEquiv p τ z χ).toRingEquiv).le)

@[simp] theorem pointCompletedLocalCharacterAction_apply (χ : rootPointStabilizer p τ z)
    (x : AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z)) :
    pointCompletedLocalCharacterAction p τ z χ x = pointCompletedLocalCharacterHom p τ z χ x := rfl

/-- The fixed algebra used in the local equivalence is exactly the fixed algebra of this action. -/
theorem mem_pointCompletedLocalFixed_iff
    (x : AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z)) :
    x ∈ pointCompletedLocalFixed p τ z ↔
      ∀ χ : rootPointStabilizer p τ z, pointCompletedLocalCharacterAction p τ z χ x = x := Iff.rfl

end CanonicalRoots
