import CanonicalRoots.AdicCompleteLift
import CanonicalRoots.OriginCotangent
import Mathlib.RingTheory.MvPowerSeries.Equiv

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (v : Fin n → ℂ)

def polynomialPoint : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ := aeval v

/-- Translate polynomial coordinates so that the given point becomes the origin. -/
def polynomialPointTranslation : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i + C (v i))) (aeval (fun i => X i - C (v i)))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, map_sub, aeval_C, algebraMap_eq, AlgHom.id_apply, add_sub_cancel_right])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, map_add, aeval_C, algebraMap_eq, AlgHom.id_apply, sub_add_cancel])

@[simp] theorem polynomialPointTranslation_X (i : Fin n) :
    polynomialPointTranslation v (X i) = X i + C (v i) := aeval_X _ _

@[simp] theorem polynomialPointTranslation_symm_X (i : Fin n) :
    (polynomialPointTranslation v).symm (X i) = X i - C (v i) := aeval_X _ _

theorem polynomialPointTranslation_origin :
    (aeval (fun _ : Fin n => (0 : ℂ))).comp (polynomialPointTranslation v).toAlgHom = polynomialPoint v := by
  apply MvPolynomial.algHom_ext
  intro i
  change aeval (fun _ : Fin n => (0 : ℂ)) (polynomialPointTranslation v (X i)) = polynomialPoint v (X i)
  simp only [polynomialPoint, polynomialPointTranslation_X, map_add, aeval_X, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, zero_add]

theorem polynomialOriginIdeal_eq_pointKer :
    polynomialOriginIdeal n = RingHom.ker (aeval (fun _ : Fin n => (0 : ℂ))).toRingHom := by
  apply Ideal.ext
  intro f
  rw [mem_polynomialOriginIdeal_iff]
  change f.coeff 0 = 0 ↔ aeval (fun _ : Fin n => (0 : ℂ)) f = 0
  simp only [show (fun _ : Fin n => (0 : ℂ)) = 0 from rfl, aeval_zero,
    Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_eq]

theorem polynomialPointTranslation_map_pointIdeal :
    (RingHom.ker (polynomialPoint v).toRingHom).map (polynomialPointTranslation v).toRingHom =
      polynomialOriginIdeal n := by
  rw [polynomialOriginIdeal_eq_pointKer]
  apply Ideal.ext
  intro f
  change f ∈ (RingHom.ker (polynomialPoint v).toRingHom).map (polynomialPointTranslation v) ↔
    f ∈ RingHom.ker (aeval (fun _ : Fin n => (0 : ℂ))).toRingHom
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (DFunLike.congr_fun (polynomialPointTranslation_origin v) g).trans hg
  · intro hf
    refine ⟨(polynomialPointTranslation v).symm f, ?_, (polynomialPointTranslation v).apply_symm_apply f⟩
    change polynomialPoint v ((polynomialPointTranslation v).symm f) = 0
    rw [← polynomialPointTranslation_origin v]
    change aeval (fun _ : Fin n => (0 : ℂ))
      (polynomialPointTranslation v ((polynomialPointTranslation v).symm f)) = 0
    rw [AlgEquiv.apply_symm_apply]
    exact hf

/-- The actual completion at an arbitrary complex polynomial point is a formal power series ring. -/
def polynomialPointCompletionEquiv :
    AdicCompletion (RingHom.ker (polynomialPoint v).toRingHom) (MvPolynomial (Fin n) ℂ) ≃ₐ[ℂ]
      MvPowerSeries (Fin n) ℂ :=
  (adicIdealEquiv _ _ (polynomialPointTranslation v) (polynomialPointTranslation_map_pointIdeal v)).trans
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).symm.restrictScalars ℂ)

@[simp] theorem polynomialPointCompletionEquiv_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    polynomialPointCompletionEquiv v
      (algebraMap (MvPolynomial (Fin n) ℂ)
        (AdicCompletion (RingHom.ker (polynomialPoint v).toRingHom) (MvPolynomial (Fin n) ℂ)) f) =
      (polynomialPointTranslation v f : MvPowerSeries (Fin n) ℂ) := by
  apply (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).injective
  change MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).symm
      (adicIdealMap _ _ (polynomialPointTranslation v).toAlgHom
        (polynomialPointTranslation_map_pointIdeal v).le
        (algebraMap (MvPolynomial (Fin n) ℂ) _ f))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (adicIdealMap_algebraMap _ _ (polynomialPointTranslation v).toAlgHom
    (polynomialPointTranslation_map_pointIdeal v).le f).trans
    (MvPowerSeries.toAdicCompletion_coe (polynomialPointTranslation v f)).symm

end CanonicalRoots
