import CanonicalRoots.PointLocalAction

noncomputable section
namespace CanonicalRoots

def rootPoint {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) : RootRing p τ →ₐ[ℂ] ℂ :=
  z.comp (rootSubalgebra p τ).val

/-- The inclusion R → T induces the map between the local rings at the corresponding points. -/
def rootPointLocalMap {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) :
    AugmentationLocalRing (rootPoint p τ z) →ₐ[ℂ] AugmentationLocalRing z :=
  IsLocalization.liftAlgHom (f :=
    (Algebra.algHom ℂ (AmbientRing p) (AugmentationLocalRing z)).comp (rootSubalgebra p τ).val)
    (M := (RingHom.ker (rootPoint p τ z).toRingHom).primeCompl) (by
      intro y
      exact IsLocalization.map_units (AugmentationLocalRing z)
        (⟨(y.val : AmbientRing p), y.property⟩ : (RingHom.ker z.toRingHom).primeCompl))

@[simp] theorem rootPointLocalMap_algebraMap {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) (r : RootRing p τ) :
    rootPointLocalMap p τ z
      (algebraMap (RootRing p τ) (AugmentationLocalRing (rootPoint p τ z)) r) =
      algebraMap (AmbientRing p) (AugmentationLocalRing z) (r : AmbientRing p) :=
  IsLocalization.lift_eq _ _

/-- The image of the root local ring is fixed by the point stabilizer.
No equality with the stabilizer fixed local ring is asserted here. -/
theorem rootPointLocalMap_fixed {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) (χ : rootPointStabilizer p τ z)
    (r : AugmentationLocalRing (rootPoint p τ z)) :
    pointLocalCharacterEquiv p τ z χ (rootPointLocalMap p τ z r) = rootPointLocalMap p τ z r := by
  have he : (pointLocalCharacterEquiv p τ z χ).toAlgHom.comp (rootPointLocalMap p τ z) =
      rootPointLocalMap p τ z := by
    apply IsLocalization.algHom_ext (RingHom.ker (rootPoint p τ z).toRingHom).primeCompl
    apply AlgHom.ext
    intro x
    change pointLocalCharacterEquiv p τ z χ (rootPointLocalMap p τ z
      (algebraMap (RootRing p τ) (AugmentationLocalRing (rootPoint p τ z)) x)) = _
    rw [rootPointLocalMap_algebraMap, pointLocalCharacterEquiv_algebraMap,
      rootSubalgebra_le_characterFixed p τ x.property χ.val]
    exact (rootPointLocalMap_algebraMap p τ z x).symm
  exact DFunLike.congr_fun he r

end CanonicalRoots
