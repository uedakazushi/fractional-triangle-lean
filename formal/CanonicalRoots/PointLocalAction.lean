import CanonicalRoots.PointStabilizer
import CanonicalRoots.HypersurfaceNonregular

noncomputable section
namespace CanonicalRoots

theorem stabilizer_preserves_primeCompl {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) (χ : rootPointStabilizer p τ z) :
    Submonoid.map (ambientCharacterEquiv p τ χ.val) (RingHom.ker z.toRingHom).primeCompl =
      (RingHom.ker z.toRingHom).primeCompl := by
  apply Submonoid.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change z (ambientCharacterHom p τ χ.val y) ≠ 0
    have he := DFunLike.congr_fun χ.property y
    change z (ambientCharacterHom p τ χ.val y) = z y at he
    rw [he]
    exact hy
  · intro hx
    refine ⟨(ambientCharacterEquiv p τ χ.val).symm x, ?_,
      (ambientCharacterEquiv p τ χ.val).apply_symm_apply x⟩
    change z ((ambientCharacterEquiv p τ χ.val).symm x) ≠ 0
    have he := DFunLike.congr_fun χ.property ((ambientCharacterEquiv p τ χ.val).symm x)
    change z (ambientCharacterEquiv p τ χ.val ((ambientCharacterEquiv p τ χ.val).symm x)) = _ at he
    rw [AlgEquiv.apply_symm_apply] at he
    rw [← he]
    exact hx

/-- Only the point stabilizer is used to act on its actual local ring. -/
def pointLocalCharacterEquiv {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) (χ : rootPointStabilizer p τ z) :
    AugmentationLocalRing z ≃ₐ[ℂ] AugmentationLocalRing z :=
  IsLocalization.algEquivOfAlgEquiv (AugmentationLocalRing z) (AugmentationLocalRing z)
    (ambientCharacterEquiv p τ χ.val) (stabilizer_preserves_primeCompl p τ z χ)

@[simp] theorem pointLocalCharacterEquiv_algebraMap {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) (χ : rootPointStabilizer p τ z) (x : AmbientRing p) :
    pointLocalCharacterEquiv p τ z χ (algebraMap (AmbientRing p) (AugmentationLocalRing z) x) =
      algebraMap (AmbientRing p) (AugmentationLocalRing z) (ambientCharacterHom p τ χ.val x) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ x

/-- The stabilizer group acts by complex algebra automorphisms of the localized quotient. -/
def pointLocalCharacterAction {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) :
    rootPointStabilizer p τ z →* (AugmentationLocalRing z ≃ₐ[ℂ] AugmentationLocalRing z) where
  toFun := pointLocalCharacterEquiv p τ z
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply IsLocalization.algHom_ext (RingHom.ker z.toRingHom).primeCompl
    apply AlgHom.ext
    intro x
    change pointLocalCharacterEquiv p τ z 1 (algebraMap (AmbientRing p) (AugmentationLocalRing z) x) = _
    rw [pointLocalCharacterEquiv_algebraMap]
    change algebraMap (AmbientRing p) (AugmentationLocalRing z) (ambientCharacterHom p τ 1 x) = _
    rw [ambientCharacterHom_one]
    rfl
  map_mul' χ ψ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply IsLocalization.algHom_ext (RingHom.ker z.toRingHom).primeCompl
    apply AlgHom.ext
    intro x
    change pointLocalCharacterEquiv p τ z (χ * ψ) (algebraMap (AmbientRing p) (AugmentationLocalRing z) x) =
      pointLocalCharacterEquiv p τ z χ (pointLocalCharacterEquiv p τ z ψ
        (algebraMap (AmbientRing p) (AugmentationLocalRing z) x))
    simp only [pointLocalCharacterEquiv_algebraMap]
    exact congrArg (algebraMap (AmbientRing p) (AugmentationLocalRing z))
      (DFunLike.congr_fun (ambientCharacterHom_mul p τ χ.val ψ.val) x)

end CanonicalRoots
