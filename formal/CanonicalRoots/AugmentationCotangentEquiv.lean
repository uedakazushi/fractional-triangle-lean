import CanonicalRoots.QuotientCotangent

noncomputable section
namespace CanonicalRoots

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  (εA : A →ₐ[ℂ] ℂ) (εB : B →ₐ[ℂ] ℂ) (e : A ≃ₐ[ℂ] B)
  (he : εB.comp e.toAlgHom = εA)

include he in
theorem augmentationKer_map_equiv :
    (RingHom.ker εA.toRingHom).map e.toRingHom = RingHom.ker εB.toRingHom := by
  apply Ideal.ext
  intro x
  change x ∈ (RingHom.ker εA.toRingHom).map e ↔ x ∈ RingHom.ker εB.toRingHom
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (AlgHom.congr_fun he y).trans hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change εA (e.symm x) = 0
    rw [← AlgHom.congr_fun he (e.symm x)]
    change εB (e (e.symm x)) = 0
    rw [e.apply_symm_apply]
    exact hx

/-- A point-preserving algebra equivalence preserves the actual augmentation cotangent space. -/
def augmentationCotangentEquiv :
    (RingHom.ker εA.toRingHom).Cotangent ≃ₗ[ℂ] (RingHom.ker εB.toRingHom).Cotangent :=
  (quotientCotangentEquiv (RingHom.ker εA.toRingHom) e.toAlgHom e.surjective (by
    intro x hx
    have hz : x = 0 := e.injective (hx.trans (map_zero _).symm)
    rw [hz]
    exact Ideal.zero_mem _)).trans
      ((Ideal.Cotangent.equivOfEq _ _ (augmentationKer_map_equiv εA εB e he)).restrictScalars ℂ)

end CanonicalRoots
