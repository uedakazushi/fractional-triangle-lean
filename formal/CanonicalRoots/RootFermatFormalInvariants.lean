import CanonicalRoots.FermatChartEquivariance
import CanonicalRoots.RootPointInvariantEquiv
import CanonicalRoots.CompletedInvariantCotangent

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
  (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0) (hv0 : v 0 ≠ 0)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The actual completed root local ring is the stabilizer fixed ring in the actual
completion of the polynomial coordinate chart. No invariant-ring identification is assumed. -/
def rootFermatCompletedInvariantChartEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) ≃+*
        fermatTailCompletedFixed p τ v hv :=
  (augmentationCompletionEquiv (rootPoint p τ (fermatPoint p v hv))).symm.toRingEquiv.trans
    ((rootPointCompletedInvariantEquiv p τ hp ha hτ (fermatPoint p v hv)).toRingEquiv.trans
      (fermatPointFixedChartEquiv p τ v hv (lt_of_lt_of_le (by decide : 0 < 2) (hp.1 0)) hv0))

include hp ha hτ hv0 in
theorem fermatTailCompletedFixed_isLocalRing : IsLocalRing (fermatTailCompletedFixed p τ v hv) := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  exact (rootFermatCompletedInvariantChartEquiv p τ hp ha hτ v hv hv0).isLocalRing

include hp ha hτ hv0 in
/-- The chart invariant ring has the original root local ring's cotangent dimension. -/
theorem rootFermatChart_embeddingDim :
    letI := fermatTailCompletedFixed_isLocalRing p τ hp ha hτ v hv hv0
    (IsLocalRing.maximalIdeal (fermatTailCompletedFixed p τ v hv)).spanFinrank =
      Module.finrank (IsLocalRing.ResidueField
        (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
        (IsLocalRing.CotangentSpace (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv)))) := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  let : IsLocalRing (fermatTailCompletedFixed p τ v hv) :=
    fermatTailCompletedFixed_isLocalRing p τ hp ha hτ v hv hv0
  rw [localCompletion_embeddingDim_equiv
    (rootFermatCompletedInvariantChartEquiv p τ hp ha hτ v hv hv0),
    IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]

end CanonicalRoots
