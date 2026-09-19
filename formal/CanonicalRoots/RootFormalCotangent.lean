import CanonicalRoots.FermatPowerSeriesInvariants
import CanonicalRoots.PowerSeriesInvariantCotangent
import CanonicalRoots.AugmentedLocalCotangent

noncomputable section
namespace CanonicalRoots
open IsLocalRing

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ) (hv0 : v 0 ≠ 0)

include hp ha hτ hv0 in
theorem rootFormal_maximalIdeal_fg :
    letI := fermatPowerSeriesFixed_isLocalRing p τ v hv hp ha hτ hv0
    (maximalIdeal (powerSeriesDiagonalFixed (fermatTailWeights p τ v hv))).FG := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  let : IsLocalRing (powerSeriesDiagonalFixed (fermatTailWeights p τ v hv)) :=
    fermatPowerSeriesFixed_isLocalRing p τ v hv hp ha hτ hv0
  exact localCompletion_maximalIdeal_fg_equiv
    (rootFermatPowerSeriesInvariantEquiv p τ v hv hp ha hτ hv0)

include hp ha hτ hv0 in
theorem rootFormal_cotangent_finite :
    Module.Finite ℂ (powerSeriesDiagonalOriginIdeal (fermatTailWeights p τ v hv)).Cotangent := by
  let : IsLocalRing (powerSeriesDiagonalFixed (fermatTailWeights p τ v hv)) :=
    fermatPowerSeriesFixed_isLocalRing p τ v hv hp ha hτ hv0
  exact augmentationCotangent_finite_of_local_fg _ (rootFormal_maximalIdeal_fg p τ v hv hp ha hτ hv0)

include hp ha hτ hv0 in
/-- Coefficient computations in the formal invariant chart give the exact original local cotangent dimension. -/
theorem rootFormal_cotangent_finrank :
    Module.finrank ℂ (powerSeriesDiagonalOriginIdeal (fermatTailWeights p τ v hv)).Cotangent =
      Module.finrank (ResidueField (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
        (CotangentSpace (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv)))) := by
  let : IsLocalRing (powerSeriesDiagonalFixed (fermatTailWeights p τ v hv)) :=
    fermatPowerSeriesFixed_isLocalRing p τ v hv hp ha hτ hv0
  rw [augmentationCotangent_finrank_of_local,
    ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg
      (rootFormal_maximalIdeal_fg p τ v hv hp ha hτ hv0)]
  exact rootFermatPowerSeries_embeddingDim p τ v hv hp ha hτ hv0

include hp ha hτ hv0 in
/-- Independent indecomposable invariant monomials yield a lower bound in the original root local ring. -/
theorem rootPointLocal_cotangent_ge_of_monomials {ι : Type*} [Fintype ι]
    (d : ι → Fin n →₀ ℕ)
    (hd : ∀ i, DiagonalIndecomposableExponent (fermatTailWeights p τ v hv) (d i))
    (hi : Function.Injective d) :
    Fintype.card ι ≤
      Module.finrank (ResidueField (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
        (CotangentSpace (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv)))) := by
  let : Module.Finite ℂ (powerSeriesDiagonalOriginIdeal (fermatTailWeights p τ v hv)).Cotangent :=
    rootFormal_cotangent_finite p τ v hv hp ha hτ hv0
  rw [← rootFormal_cotangent_finrank p τ v hv hp ha hτ hv0]
  exact (diagonalCotangentMonomials_linearIndependent _ d hd hi).fintype_card_le_finrank

end CanonicalRoots
