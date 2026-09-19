import CanonicalRoots.LocalCotangent

noncomputable section
namespace CanonicalRoots
open MvPolynomial IsLocalRing

section Augmented
variable {A : Type*} [CommRing A] [Algebra ℂ A] (ε : A →ₐ[ℂ] ℂ)

theorem augmentation_surjective : Function.Surjective ε := by
  intro z
  exact ⟨algebraMap ℂ A z, by simp⟩

instance augmentationKer_isMaximal : (RingHom.ker ε.toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ε.toRingHom (augmentation_surjective ε)

abbrev AugmentationLocalRing := Localization.AtPrime (RingHom.ker ε.toRingHom)

def augmentationLocalResidueEquiv : ResidueField (AugmentationLocalRing ε) ≃ₐ[ℂ] ℂ := by
  exact (localResidueEquiv (RingHom.ker ε.toRingHom) (AugmentationLocalRing ε)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective ε))

/-- The localized cotangent dimension is computed over its actual residue field. -/
theorem augmentationLocalCotangent_finrank :
    Module.finrank (ResidueField (AugmentationLocalRing ε))
      (CotangentSpace (AugmentationLocalRing ε)) =
      Module.finrank ℂ (RingHom.ker ε.toRingHom).Cotangent := by
  let : IsScalarTower ℂ (ResidueField (AugmentationLocalRing ε))
      (CotangentSpace (AugmentationLocalRing ε)) :=
    IsScalarTower.of_algebraMap_smul (fun a z => by
      change algebraMap (AugmentationLocalRing ε) (ResidueField (AugmentationLocalRing ε))
        (algebraMap ℂ (AugmentationLocalRing ε) a) • z = a • z
      rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul])
  have hres : Module.finrank ℂ (ResidueField (AugmentationLocalRing ε)) = 1 := by
    rw [(augmentationLocalResidueEquiv ε).toLinearEquiv.finrank_eq]
    simp
  have hdim := Module.finrank_mul_finrank ℂ (ResidueField (AugmentationLocalRing ε))
    (CotangentSpace (AugmentationLocalRing ε))
  rw [hres, one_mul] at hdim
  exact hdim.trans (localCotangentEquiv (RingHom.ker ε.toRingHom)
    (AugmentationLocalRing ε)).finrank_eq.symm
end Augmented

abbrev PresentedOriginLocalRing {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (h0 : f.coeff 0 = 0) :=
  AugmentationLocalRing (presentedAugmentation f h0)

theorem presentedLocalCotangent_finrank {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : HasNoConstantOrLinear f) :
    Module.finrank (ResidueField (PresentedOriginLocalRing f hf.1))
      (CotangentSpace (PresentedOriginLocalRing f hf.1)) = n := by
  rw [augmentationLocalCotangent_finrank, ← presentedOriginIdeal_eq_ker f hf.1]
  exact presentedOriginCotangent_finrank f hf

/-- A nonzero equation cuts the Krull dimension by at least one. -/
theorem presented_krullDim_succ_le {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0) :
    ringKrullDim (PresentedRing f) + 1 ≤ n := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    ((mem_nonZeroDivisors_iff_ne_zero).mpr hf)
  simpa using h

theorem presentedLocal_krullDim_succ_le {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (h0 : f.coeff 0 = 0) (hf : f ≠ 0) :
    ringKrullDim (PresentedOriginLocalRing f h0) + 1 ≤ n := by
  have hle : ringKrullDim (PresentedOriginLocalRing f h0) ≤ ringKrullDim (PresentedRing f) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (RingHom.ker (presentedAugmentation f h0).toRingHom)]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  exact (add_le_add hle (le_refl 1)).trans (presented_krullDim_succ_le f hf)

/-- Any nonzero hypersurface relation with no linear term gives a nonregular local ring
at the origin. This uses the actual localization, residue field and Krull dimension. -/
theorem presented_origin_not_regular {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : HasNoConstantOrLinear f) (hne : f ≠ 0) :
    ¬ IsRegularLocalRing (PresentedOriginLocalRing f hf.1) := by
  intro hreg
  let : IsRegularLocalRing (PresentedOriginLocalRing f hf.1) := hreg
  have hdim := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (PresentedOriginLocalRing f hf.1)).mp hreg
  rw [presentedLocalCotangent_finrank f hf] at hdim
  have hle := presentedLocal_krullDim_succ_le f hf.1 hne
  rw [← hdim] at hle
  exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self n)) hle

end CanonicalRoots
