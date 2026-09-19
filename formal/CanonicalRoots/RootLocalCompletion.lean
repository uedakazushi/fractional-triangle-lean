import CanonicalRoots.RootCompletedAlgebra
import CanonicalRoots.LocalCompletion
import CanonicalRoots.RootPointLocalMap

noncomputable section
namespace CanonicalRoots

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The completed local root ring at an actual complex point is the fixed algebra of the
whole completed finite extension. Passing to one ambient point is a separate step. -/
def rootLocalCompletedRingEquiv {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (ε : RootRing p τ →ₐ[ℂ] ℂ) :
    AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing ε))
      (AugmentationLocalRing ε) ≃+*
      completedRootFixed p τ (RingHom.ker ε.toRingHom) :=
  (augmentationCompletionEquiv ε).symm.toRingEquiv.trans
    (rootCompletedAlgebraEquiv p τ (RingHom.ker ε.toRingHom) hp ha hτ).toRingEquiv

end CanonicalRoots
