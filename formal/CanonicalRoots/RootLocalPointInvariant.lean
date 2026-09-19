import CanonicalRoots.RootPointInvariantEquiv
import CanonicalRoots.LocalCompletionNaturality
import CanonicalRoots.RootLocalCompletion

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (z : AmbientRing p →ₐ[ℂ] ℂ)

/-- Complete the actual stabilizer automorphism of the actual ambient local ring. -/
def pointCompletedLocalCharacterHom (χ : rootPointStabilizer p τ z) :
    AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z)
      →ₐ[ℂ]
    AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z) :=
  adicIdealMap _ _ (pointLocalCharacterEquiv p τ z χ).toAlgHom
    (IsLocalRing.map_ringEquiv_maximalIdeal (pointLocalCharacterEquiv p τ z χ).toRingEquiv).le

theorem pointCompleted_local_conjugate (χ : rootPointStabilizer p τ z)
    (x : AdicCompletion (RingHom.ker z.toRingHom) (AmbientRing p)) :
    augmentationCompletionEquiv z (pointCompletedCharacterHom p τ z χ x) =
      pointCompletedLocalCharacterHom p τ z χ (augmentationCompletionEquiv z x) := by
  exact localCompletionEquiv_natural (RingHom.ker z.toRingHom)
    (ambientCharacterHom p τ χ.val) (pointLocalCharacterEquiv p τ z χ).toAlgHom
    ((augmentation_map_kernel_iff z (ambientCharacterEquiv p τ χ.val)).mpr χ.property).le
    (IsLocalRing.map_ringEquiv_maximalIdeal (pointLocalCharacterEquiv p τ z χ).toRingEquiv).le
    (pointLocalCharacterEquiv_algebraMap p τ z χ) x

/-- Fixed algebra of the point stabilizer on the completion of the original local ring. -/
def pointCompletedLocalFixed : Subalgebra ℂ
    (AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing z)) (AugmentationLocalRing z)) where
  carrier := {x | ∀ χ : rootPointStabilizer p τ z, pointCompletedLocalCharacterHom p τ z χ x = x}
  zero_mem' χ := map_zero _
  one_mem' χ := map_one _
  add_mem' hx hy χ := by rw [map_add, hx χ, hy χ]
  mul_mem' hx hy χ := by rw [map_mul, hx χ, hy χ]
  algebraMap_mem' r χ := (pointCompletedLocalCharacterHom p τ z χ).commutes r

def pointCompletedFixedLocalEquiv : pointCompletedFixed p τ z ≃+* pointCompletedLocalFixed p τ z where
  toFun x := ⟨augmentationCompletionEquiv z x.val, fun χ => by
    rw [← pointCompleted_local_conjugate, x.property χ]⟩
  invFun x := ⟨(augmentationCompletionEquiv z).symm x.val, fun χ => by
    apply (augmentationCompletionEquiv z).injective
    rw [pointCompleted_local_conjugate, AlgEquiv.apply_symm_apply]
    exact x.property χ⟩
  left_inv x := Subtype.ext ((augmentationCompletionEquiv z).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((augmentationCompletionEquiv z).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((augmentationCompletionEquiv z).map_mul x.val y.val)
  map_add' x y := Subtype.ext ((augmentationCompletionEquiv z).map_add x.val y.val)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The complete actual local root ring equals the stabilizer invariants in the complete
actual ambient local ring. All finiteness, transitivity and descent statements are proved. -/
def rootLocalPointCompletedInvariantEquiv (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (hτ : IsCanonicalRoot p a τ) :
    AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing (rootPoint p τ z)))
      (AugmentationLocalRing (rootPoint p τ z)) ≃+* pointCompletedLocalFixed p τ z :=
  ((rootLocalCompletedRingEquiv p hp ha τ hτ (rootPoint p τ z)).trans
    (rootCompletedFixedPointEquiv p τ hp ha hτ z).toRingEquiv).trans
      (pointCompletedFixedLocalEquiv p τ z)

end CanonicalRoots
