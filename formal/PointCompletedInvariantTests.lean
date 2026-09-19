import CanonicalRoots.PointCompletedLocalAction

noncomputable section
namespace CanonicalRoots.PointCompletedInvariantTests

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Check the complete local statement with only the original admissibility/root hypotheses. -/
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (z : AmbientRing p →ₐ[ℂ] ℂ) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing (rootPoint p τ z)))
      (AugmentationLocalRing (rootPoint p τ z)) ≃+* pointCompletedLocalFixed p τ z) :=
  ⟨rootLocalPointCompletedInvariantEquiv p τ z hp ha hτ⟩

/-- Inverse characters are actual inverse automorphisms of the completed local ring. -/
example {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (χ : rootPointStabilizer p τ z)
    (x : AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z)) :
    pointCompletedLocalCharacterHom p τ z χ⁻¹ (pointCompletedLocalCharacterHom p τ z χ x) = x := by
  have he := (pointCompletedLocalCharacterAction p τ z).map_mul χ⁻¹ χ
  rw [inv_mul_cancel χ, map_one] at he
  exact (DFunLike.congr_fun he x).symm

/-- The newly proved descent map is onto the original stabilizer fixed algebra. -/
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (c : pointCompletedFixed p τ z) :
    ∃ x : AdicCompletion (RingHom.ker (rootPoint p τ z).toRingHom) (RootRing p τ),
      rootPointCompletedInvariantEquiv p τ hp ha hτ z x = c :=
  (rootPointCompletedInvariantEquiv p τ hp ha hτ z).surjective c

end CanonicalRoots.PointCompletedInvariantTests
