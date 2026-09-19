import CanonicalRoots.RootFermatFormalInvariants
import CanonicalRoots.PolynomialCompletionEquivariance
import CanonicalRoots.PowerSeriesDiagonalFixed

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0)

def fermatTailPowerSeriesEquiv : FermatTailCompletion v ≃ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  polynomialPointCompletionEquiv (fun i => v i.succ)

def fermatTailWeights (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (i : Fin n) : ℂ :=
  rootCharacterValue p τ χ.val (xDegree p i.succ)

theorem fermatTailWeights_fix_point (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (i : Fin n) :
    fermatTailWeights p τ v hv χ i * v i.succ = v i.succ := by
  simpa only [fermatTailWeights, fermatPoint_X] using
    (mem_rootPointStabilizer_iff_coordinates p τ (fermatPoint p v hv) χ.val).mp χ.property i.succ

/-- The original stabilizer acts coefficientwise in the translated formal power-series coordinates. -/
theorem fermatTailPowerSeriesEquiv_equivariant
    (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (x : FermatTailCompletion v) :
    fermatTailPowerSeriesEquiv v (fermatTailCompletedCharacterAction p τ v hv χ x) =
      MvPowerSeries.rescaleAlgHom (fermatTailWeights p τ v hv χ) (fermatTailPowerSeriesEquiv v x) :=
  polynomialPointCompletionEquiv_diagonal (fun i => v i.succ) (fermatTailWeights p τ v hv χ)
    (fermatTailWeights_fix_point p τ v hv χ) x

/-- Restrict the actual power-series coordinate equivalence to all stabilizer invariants. -/
def fermatTailFixedPowerSeriesEquiv : fermatTailCompletedFixed p τ v hv ≃ₐ[ℂ]
    powerSeriesDiagonalFixed (fermatTailWeights p τ v hv) where
  toFun x := ⟨fermatTailPowerSeriesEquiv v x.val, fun χ => by
    rw [← fermatTailPowerSeriesEquiv_equivariant, x.property χ]⟩
  invFun x := ⟨(fermatTailPowerSeriesEquiv v).symm x.val, fun χ => by
    apply (fermatTailPowerSeriesEquiv v).injective
    rw [fermatTailPowerSeriesEquiv_equivariant, AlgEquiv.apply_symm_apply]
    exact x.property χ⟩
  left_inv x := Subtype.ext ((fermatTailPowerSeriesEquiv v).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((fermatTailPowerSeriesEquiv v).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((fermatTailPowerSeriesEquiv v).map_add x.val y.val)
  map_mul' x y := Subtype.ext ((fermatTailPowerSeriesEquiv v).map_mul x.val y.val)
  commutes' c := Subtype.ext ((fermatTailPowerSeriesEquiv v).commutes c)

variable (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ) (hv0 : v 0 ≠ 0)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The completed original root local ring is the explicit diagonal-invariant power-series ring. -/
def rootFermatPowerSeriesInvariantEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) ≃+*
        powerSeriesDiagonalFixed (fermatTailWeights p τ v hv) :=
  (rootFermatCompletedInvariantChartEquiv p τ hp ha hτ v hv hv0).trans
    (fermatTailFixedPowerSeriesEquiv p τ v hv).toRingEquiv

include hp ha hτ hv0 in
theorem fermatPowerSeriesFixed_isLocalRing :
    IsLocalRing (powerSeriesDiagonalFixed (fermatTailWeights p τ v hv)) := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  exact (rootFermatPowerSeriesInvariantEquiv p τ v hv hp ha hτ hv0).isLocalRing

include hp ha hτ hv0 in
theorem rootFermatPowerSeries_embeddingDim :
    letI := fermatPowerSeriesFixed_isLocalRing p τ v hv hp ha hτ hv0
    (IsLocalRing.maximalIdeal (powerSeriesDiagonalFixed (fermatTailWeights p τ v hv))).spanFinrank =
      Module.finrank (IsLocalRing.ResidueField
        (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
        (IsLocalRing.CotangentSpace (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv)))) := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  let : IsLocalRing (powerSeriesDiagonalFixed (fermatTailWeights p τ v hv)) :=
    fermatPowerSeriesFixed_isLocalRing p τ v hv hp ha hτ hv0
  rw [localCompletion_embeddingDim_equiv
    (rootFermatPowerSeriesInvariantEquiv p τ v hv hp ha hτ hv0),
    IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]

end CanonicalRoots
