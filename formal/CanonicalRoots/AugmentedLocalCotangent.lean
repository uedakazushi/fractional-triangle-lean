import CanonicalRoots.CompletedInvariantCotangent

noncomputable section
namespace CanonicalRoots
open IsLocalRing

variable {B : Type*} [CommRing B] [Algebra ℂ B] [IsLocalRing B] (ε : B →ₐ[ℂ] ℂ)

theorem augmentationKer_eq_maximalIdeal : RingHom.ker ε.toRingHom = maximalIdeal B :=
  IsLocalRing.eq_maximalIdeal (augmentationKer_isMaximal ε)

def augmentationResidueEquiv : ResidueField B ≃ₐ[ℂ] ℂ :=
  (Ideal.quotientEquivAlgOfEq ℂ (augmentationKer_eq_maximalIdeal ε).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective ε))

/-- Compare the augmentation cotangent dimension with the actual local residue-field dimension. -/
theorem augmentationCotangent_finrank_of_local :
    Module.finrank ℂ (RingHom.ker ε.toRingHom).Cotangent =
      Module.finrank (ResidueField B) (CotangentSpace B) := by
  let : IsScalarTower ℂ (ResidueField B) (CotangentSpace B) :=
    IsScalarTower.of_algebraMap_smul (fun a z => by
      change algebraMap B (ResidueField B) (algebraMap ℂ B a) • z = a • z
      rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul])
  have he : (RingHom.ker ε.toRingHom).Cotangent ≃ₗ[ℂ] CotangentSpace B :=
    (Ideal.Cotangent.equivOfEq _ _ (augmentationKer_eq_maximalIdeal ε)).restrictScalars ℂ
  rw [he.finrank_eq]
  have hres : Module.finrank ℂ (ResidueField B) = 1 := by
    rw [(augmentationResidueEquiv ε).toLinearEquiv.finrank_eq]
    simp
  have h := Module.finrank_mul_finrank ℂ (ResidueField B) (CotangentSpace B)
  rw [hres, one_mul] at h
  exact h.symm

/-- A finitely generated maximal ideal gives a finite-dimensional augmentation cotangent space,
without assuming that the whole local ring is Noetherian. -/
theorem augmentationCotangent_finite_of_local_fg (hfg : (maximalIdeal B).FG) :
    Module.Finite ℂ (RingHom.ker ε.toRingHom).Cotangent := by
  let I := RingHom.ker ε.toRingHom
  have hI : I.FG := by change (RingHom.ker ε.toRingHom).FG; rw [augmentationKer_eq_maximalIdeal ε]; exact hfg
  let : Module.Finite B I := Module.Finite.iff_fg.mpr hI
  let : Module.Finite B I.Cotangent := Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
  let : Module.Finite (B ⧸ I) I.Cotangent := Module.Finite.of_restrictScalars_finite B _ _
  let : Module.Finite ℂ (B ⧸ I) := Module.Finite.of_injective
    (Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective ε)).toLinearMap
    (Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective ε)).injective
  let : IsScalarTower ℂ (B ⧸ I) I.Cotangent :=
    IsScalarTower.of_algebraMap_smul (fun a z => by
      change algebraMap B (B ⧸ I) (algebraMap ℂ B a) • z = a • z
      rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul])
  exact Module.Finite.trans (B ⧸ I) I.Cotangent

/-- Any ring isomorphic to a Noetherian local ring's completion has a finitely generated maximal ideal. -/
theorem localCompletion_maximalIdeal_fg_equiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S]
    (e : AdicCompletion (maximalIdeal R) R ≃+* S) : (maximalIdeal S).FG := by
  rw [← map_ringEquiv_maximalIdeal e]
  have h : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (Ideal.fg_of_isNoetherianRing (maximalIdeal R)).map _
  exact h.map e.toRingHom

end CanonicalRoots
