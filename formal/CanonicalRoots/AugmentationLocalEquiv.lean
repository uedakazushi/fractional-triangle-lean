import CanonicalRoots.HypersurfaceNonregular

noncomputable section
namespace CanonicalRoots

section
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  (εA : A →ₐ[ℂ] ℂ) (εB : B →ₐ[ℂ] ℂ) (e : A ≃ₐ[ℂ] B)
  (he : εB.comp e.toAlgHom = εA)

include he

theorem augmentationEquiv_primeCompl :
    Submonoid.map e (RingHom.ker εA.toRingHom).primeCompl =
      (RingHom.ker εB.toRingHom).primeCompl := by
  apply Submonoid.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change εB (e y) ≠ 0
    have hy' := DFunLike.congr_fun he y
    change εB (e y) = εA y at hy'
    rw [hy']
    exact hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change εA (e.symm x) ≠ 0
    have hx' := DFunLike.congr_fun he (e.symm x)
    change εB (e (e.symm x)) = εA (e.symm x) at hx'
    rw [e.apply_symm_apply] at hx'
    rw [← hx']
    exact hx

/-- An algebra equivalence preserving complex points induces an equivalence of their local rings. -/
def augmentationLocalEquiv : AugmentationLocalRing εA ≃ₐ[ℂ] AugmentationLocalRing εB :=
  IsLocalization.algEquivOfAlgEquiv (AugmentationLocalRing εA) (AugmentationLocalRing εB) e
    (augmentationEquiv_primeCompl εA εB e he)

end
end CanonicalRoots
