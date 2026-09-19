import CanonicalRoots.PolynomialDiagonalAction
import CanonicalRoots.AdicCompleteExt

noncomputable section
namespace CanonicalRoots
open MvPolynomial

abbrev powerSeriesOriginIdeal (n : ℕ) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (Set.range MvPowerSeries.X)

theorem polynomialOriginIdeal_map_powerSeries (n : ℕ) :
    (polynomialOriginIdeal n).map (coeToMvPowerSeries.ringHom :
      MvPolynomial (Fin n) ℂ →+* MvPowerSeries (Fin n) ℂ) = powerSeriesOriginIdeal n := by
  change (Ideal.span (Set.range X)).map coeToMvPowerSeries.ringHom = _
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact coe_X (R := ℂ) i

variable {n : ℕ} (v : Fin n → ℂ)

theorem polynomialPointCompletionEquiv_algebraMap_mem (f : MvPolynomial (Fin n) ℂ)
    (hf : f ∈ RingHom.ker (polynomialPoint v).toRingHom) :
    polynomialPointCompletionEquiv v
      (algebraMap (MvPolynomial (Fin n) ℂ)
        (AdicCompletion (RingHom.ker (polynomialPoint v).toRingHom) (MvPolynomial (Fin n) ℂ)) f) ∈
      powerSeriesOriginIdeal n := by
  rw [polynomialPointCompletionEquiv_algebraMap, ← polynomialOriginIdeal_map_powerSeries]
  have ht : polynomialPointTranslation v f ∈ polynomialOriginIdeal n := by
    rw [← polynomialPointTranslation_map_pointIdeal v]
    exact Ideal.mem_map_of_mem (polynomialPointTranslation v).toRingHom hf
  exact Ideal.mem_map_of_mem coeToMvPowerSeries.ringHom ht

variable (w : Fin n → ℂ) (hv : ∀ i, w i * v i = v i)

def polynomialCompletedDiagonal :
    AdicCompletion (RingHom.ker (polynomialPoint v).toRingHom) (MvPolynomial (Fin n) ℂ) →ₐ[ℂ]
      AdicCompletion (RingHom.ker (polynomialPoint v).toRingHom) (MvPolynomial (Fin n) ℂ) :=
  adicIdealMap _ _ (polynomialDiagonalHom w) (polynomialDiagonal_map_pointIdeal w v hv)

/-- The actual point-completion coordinates turn the original diagonal action into
mathlib's coefficientwise rescaling of formal power series. -/
theorem polynomialPointCompletionEquiv_diagonal
    (x : AdicCompletion (RingHom.ker (polynomialPoint v).toRingHom) (MvPolynomial (Fin n) ℂ)) :
    polynomialPointCompletionEquiv v (polynomialCompletedDiagonal v w hv x) =
      MvPowerSeries.rescaleAlgHom w (polynomialPointCompletionEquiv v x) := by
  have he : (polynomialPointCompletionEquiv v).toAlgHom.comp (polynomialCompletedDiagonal v w hv) =
      (MvPowerSeries.rescaleAlgHom w).comp (polynomialPointCompletionEquiv v).toAlgHom := by
    apply adicCompletion_algHom_ext_of_base _ (Ideal.fg_of_isNoetherianRing _) (powerSeriesOriginIdeal n)
    · intro f hf
      change polynomialPointCompletionEquiv v (adicIdealMap _ _ (polynomialDiagonalHom w)
        (polynomialDiagonal_map_pointIdeal w v hv) (algebraMap (MvPolynomial (Fin n) ℂ) _ f)) ∈ _
      rw [adicIdealMap_algebraMap]
      exact polynomialPointCompletionEquiv_algebraMap_mem v (polynomialDiagonalHom w f)
        (Ideal.map_le_iff_le_comap.mp (polynomialDiagonal_map_pointIdeal w v hv) hf)
    · intro f
      change polynomialPointCompletionEquiv v (adicIdealMap _ _ (polynomialDiagonalHom w)
          (polynomialDiagonal_map_pointIdeal w v hv) (algebraMap (MvPolynomial (Fin n) ℂ) _ f)) =
        MvPowerSeries.rescaleAlgHom w (polynomialPointCompletionEquiv v
          (algebraMap (MvPolynomial (Fin n) ℂ) _ f))
      rw [adicIdealMap_algebraMap, polynomialPointCompletionEquiv_algebraMap,
        polynomialPointCompletionEquiv_algebraMap, ← polynomialDiagonalHom_powerSeries]
      exact congrArg (fun f : MvPolynomial (Fin n) ℂ => (f : MvPowerSeries (Fin n) ℂ))
        (DFunLike.congr_fun (polynomialPointTranslation_diagonal w v hv) f)
  exact DFunLike.congr_fun he x

end CanonicalRoots
