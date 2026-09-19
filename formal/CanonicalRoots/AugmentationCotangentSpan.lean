import CanonicalRoots.QuotientCotangent

noncomputable section
namespace CanonicalRoots

variable {A : Type*} [CommRing A] [Algebra ℂ A] (ε : A →ₐ[ℂ] ℂ)

/-- Subtracting the value at a complex point projects the vector space onto its augmentation ideal. -/
def augmentationProjection : A →ₗ[ℂ] RingHom.ker ε.toRingHom :=
  ((LinearMap.id : A →ₗ[ℂ] A) - (Algebra.linearMap ℂ A).comp ε.toLinearMap).codRestrict
    ((RingHom.ker ε.toRingHom).restrictScalars ℂ) (by
      intro x
      change ε (x - algebraMap ℂ A (ε x)) = 0
      simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])

@[simp] theorem augmentationProjection_apply (x : A) :
    (augmentationProjection ε x : A) = x - algebraMap ℂ A (ε x) := rfl

theorem augmentationProjection_surjective : Function.Surjective (augmentationProjection ε) := by
  intro x
  refine ⟨x, Subtype.ext ?_⟩
  rw [augmentationProjection_apply, show ε (x : A) = 0 from x.property, map_zero, sub_zero]

def augmentationCotangentProjection : A →ₗ[ℂ] (RingHom.ker ε.toRingHom).Cotangent :=
  ((RingHom.ker ε.toRingHom).toCotangent.restrictScalars ℂ).comp (augmentationProjection ε)

theorem augmentationCotangentProjection_surjective :
    Function.Surjective (augmentationCotangentProjection ε) :=
  (RingHom.ker ε.toRingHom).toCotangent_surjective.comp (augmentationProjection_surjective ε)

/-- Projecting any algebra vector-space basis spans the actual cotangent space. -/
theorem augmentationCotangentBasisImage_span {ι : Type*} (b : Module.Basis ι ℂ A) :
    Submodule.span ℂ (Set.range (fun i => augmentationCotangentProjection ε (b i))) = ⊤ := by
  have h := congrArg (Submodule.map (augmentationCotangentProjection ε)) b.span_eq
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.mpr (augmentationCotangentProjection_surjective ε)] at h
  rw [← Set.range_comp] at h
  exact h

end CanonicalRoots
