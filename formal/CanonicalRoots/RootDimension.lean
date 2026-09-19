import CanonicalRoots.CanonicalFiniteFree
import CanonicalRoots.IntegralDimension
import CanonicalRoots.Target
import Mathlib.RingTheory.KrullDimension.Polynomial

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)

/-- The canonical finite free extension is an integral extension of the actual polynomial subalgebra. -/
theorem canonicalRoot_integral :
    Algebra.IsIntegral (canonicalPowerSubalgebra p hp ha τ hτ) (RootRing p τ) := by
  let : Module.Finite (canonicalPowerSubalgebra p hp ha τ hτ) (RootRing p τ) :=
    canonicalRoot_finite p hp ha τ hτ
  infer_instance

include hp ha hτ in
/-- Exact Krull dimension of every admissible actual root ring, without a hypersurface premise. -/
theorem canonicalRoot_krullDim : ringKrullDim (RootRing p τ) = n := by
  let A := canonicalPowerSubalgebra p hp ha τ hτ
  let : Algebra.IsIntegral A (RootRing p τ) := canonicalRoot_integral p hp ha τ hτ
  rw [integral_ringKrullDim_eq A (RootRing p τ),
    ← ringKrullDim_eq_of_ringEquiv (canonicalPowerSubalgebraEquiv p hp ha τ hτ).toRingEquiv]
  simp

theorem Target.root_krullDim {r a : ℕ} (T : Target r a) :
    ringKrullDim (RootRing T.signature T.tau) = (r - 1 : ℕ) := by
  cases r with
  | zero => have h := T.dimension_input; omega
  | succ r =>
    simpa only [Nat.add_sub_cancel] using
      canonicalRoot_krullDim T.signature T.admissible T.parameter_input T.tau T.root_equation

end CanonicalRoots
