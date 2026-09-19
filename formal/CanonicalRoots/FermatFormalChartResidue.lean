import CanonicalRoots.FermatFormalChart

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (v : Fin (n + 1) → ℂ)

def fermatTailCompletedResidue : FermatTailCompletion v →ₐ[ℂ] ℂ :=
  AdicCompletion.kerProj (augmentation_surjective (fermatTailPoint v))

@[simp] theorem fermatTailCompletedResidue_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    fermatTailCompletedResidue v
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) f) = fermatTailPoint v f :=
  AdicCompletion.kerProj_of _ f

theorem fermatTailCompletedResidue_ker :
    RingHom.ker (fermatTailCompletedResidue v).toRingHom =
      (RingHom.ker (fermatTailPoint v).toRingHom).map
        (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v)) := by
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ (Ideal.fg_of_isNoetherianRing _)]
  apply Ideal.ext
  intro x
  change Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective (fermatTailPoint v))
      (AdicCompletion.evalOneₐ _ x) = 0 ↔ AdicCompletion.evalOneₐ _ x = 0
  exact map_eq_zero_iff _ (Ideal.quotientKerAlgEquivOfSurjective
    (augmentation_surjective (fermatTailPoint v))).injective

variable (p : Fin (n + 1) → ℕ) (hp : 0 < p 0) (hv : ∑ i, v i ^ p i = 0) (hv0 : v 0 ≠ 0)

@[simp] theorem fermatTailCompletedResidue_branch :
    fermatTailCompletedResidue v (fermatCompletedBranch p v hp hv hv0) = v 0 := by
  have h := fermatCompletedBranch_residue p v hp hv hv0
  rw [← fermatTailCompletedResidue_ker] at h
  change fermatTailCompletedResidue v
    (fermatCompletedBranch p v hp hv hv0 - algebraMap ℂ (FermatTailCompletion v) (v 0)) = 0 at h
  simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using h

/-- The formal chart is centered at the original Fermat point. -/
theorem fermatFormalChart_residue :
    (fermatTailCompletedResidue v).comp (fermatFormalChart p v hp hv hv0) = fermatPoint p v hv := by
  have h : ((fermatTailCompletedResidue v).comp (fermatFormalChart p v hp hv hv0)).comp
      (ambientQuotient p) = (fermatPoint p v hv).comp (ambientQuotient p) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp only [AlgHom.comp_apply, fermatFormalChart_X_zero, fermatTailCompletedResidue_branch,
        fermatPoint_X]
    | succ i => simp only [AlgHom.comp_apply, fermatFormalChart_X_succ,
        fermatTailCompletedResidue_algebraMap, fermatTailPoint, aeval_X, fermatPoint_X]
  apply AlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (fermatIdeal p) x
  exact DFunLike.congr_fun h f

/-- The chart carries the original point ideal into the completed coordinate point ideal. -/
theorem fermatFormalChart_map_pointIdeal :
    (RingHom.ker (fermatPoint p v hv).toRingHom).map (fermatFormalChart p v hp hv hv0).toRingHom ≤
      (RingHom.ker (fermatTailPoint v).toRingHom).map
        (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v)) := by
  rw [← fermatTailCompletedResidue_ker]
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change fermatTailCompletedResidue v (fermatFormalChart p v hp hv hv0 x) = 0
  exact (DFunLike.congr_fun (fermatFormalChart_residue v p hp hv hv0) x).trans hx

end CanonicalRoots
