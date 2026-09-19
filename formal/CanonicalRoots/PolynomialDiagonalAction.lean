import CanonicalRoots.PolynomialPointCompletion
import Mathlib.RingTheory.MvPowerSeries.Substitution

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (w : Fin n → ℂ)

/-- The polynomial substitution corresponding to mathlib's power-series rescaling. -/
def polynomialDiagonalHom : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (fun i => w i • X i)

@[simp] theorem polynomialDiagonalHom_X (i : Fin n) :
    polynomialDiagonalHom w (X i) = w i • X i := aeval_X _ _

theorem polynomialDiagonalHom_powerSeries (f : MvPolynomial (Fin n) ℂ) :
    (polynomialDiagonalHom w f : MvPowerSeries (Fin n) ℂ) =
      MvPowerSeries.rescaleAlgHom w (f : MvPowerSeries (Fin n) ℂ) := by
  have he : (coeToMvPowerSeries.algHom ℂ).comp (polynomialDiagonalHom w) =
      aeval (fun i => w i • MvPowerSeries.X i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, polynomialDiagonalHom_X, map_smul, coeToMvPowerSeries.algHom_apply,
      Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply, coe_X, aeval_X]
  have h := DFunLike.congr_fun he f
  simpa only [AlgHom.comp_apply, coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
    MvPowerSeries.map_id, RingHom.id_apply, MvPowerSeries.rescaleAlgHom, MvPowerSeries.substAlgHom_coe, Pi.smul_def'] using h

variable (v : Fin n → ℂ) (hv : ∀ i, w i * v i = v i)

include hv in
theorem polynomialPoint_diagonal : (polynomialPoint v).comp (polynomialDiagonalHom w) = polynomialPoint v := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, polynomialDiagonalHom_X, map_smul, polynomialPoint, aeval_X,
    smul_eq_mul] using hv i

include hv in
theorem polynomialDiagonal_map_pointIdeal :
    (RingHom.ker (polynomialPoint v).toRingHom).map (polynomialDiagonalHom w).toRingHom ≤
      RingHom.ker (polynomialPoint v).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  exact (DFunLike.congr_fun (polynomialPoint_diagonal w v hv) f).trans hf

include hv in
/-- Translation to a fixed point commutes with its diagonal action. -/
theorem polynomialPointTranslation_diagonal :
    (polynomialPointTranslation v).toAlgHom.comp (polynomialDiagonalHom w) =
      (polynomialDiagonalHom w).comp (polynomialPointTranslation v).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change polynomialPointTranslation v (polynomialDiagonalHom w (X i)) =
    polynomialDiagonalHom w (polynomialPointTranslation v (X i))
  rw [polynomialDiagonalHom_X, map_smul, polynomialPointTranslation_X, map_add,
    polynomialDiagonalHom_X]
  simp only [smul_add, smul_eq_C_mul, ← map_mul, hv, aeval_C, polynomialDiagonalHom, algebraMap_eq]

end CanonicalRoots
