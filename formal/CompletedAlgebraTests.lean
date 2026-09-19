import CanonicalRoots.RootLocalCompletion

noncomputable section
namespace CanonicalRoots.CompletedAlgebraTests

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (ε : RootRing p τ →ₐ[ℂ] ℂ) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing ε))
      (AugmentationLocalRing ε) ≃+*
      completedRootFixed p τ (RingHom.ker ε.toRingHom)) :=
  ⟨rootLocalCompletedRingEquiv p hp ha τ hτ ε⟩

/-- Verify multiplication in the actual completed fixed algebra, beyond a linear equivalence. -/
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (I : Ideal (RootRing p τ))
    (x y : AdicCompletion I (RootRing p τ)) :
    rootCompletedAlgebraEquiv p τ I hp ha hτ (x * y) =
      rootCompletedAlgebraEquiv p τ I hp ha hτ x * rootCompletedAlgebraEquiv p τ I hp ha hτ y :=
  map_mul _ x y

/-- The action of an inverse character really inverts the action on the completed ring. -/
example {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (I : Ideal (RootRing p τ))
    (χ : RootCharacter p τ) (x : AmbientRootCompletion p τ I) :
    completedRootCharacterAction p τ I χ⁻¹ (completedRootCharacterAction p τ I χ x) = x := by
  have he := (completedRootCharacterAction p τ I).map_mul χ⁻¹ χ
  rw [inv_mul_cancel χ, map_one] at he
  exact (DFunLike.congr_fun he x).symm

end CanonicalRoots.CompletedAlgebraTests

#check CanonicalRoots.rootCompletedAlgebraEquiv
#check CanonicalRoots.rootLocalCompletedRingEquiv
