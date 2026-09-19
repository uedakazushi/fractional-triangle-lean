import CanonicalRoots.RootFiniteFree

noncomputable section
namespace CanonicalRoots

def canonicalRootScale {n : ℕ} (p : Fin n → ℕ) (a : ℕ) : ℕ :=
  (signatureIndex p / (a : ℤ)).toNat

section Canonical
variable {n a : ℕ} (p : Fin (n + 1) → ℕ)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
theorem canonicalRootScale_pos : 0 < canonicalRootScale p a := by
  have := canonicalRoot_scale_positive p hp ha τ hτ
  unfold canonicalRootScale
  omega

/-- The polynomial subalgebra is defined inside the actual root ring, with the canonical
denominator and scale. No additional lattice equation is assumed. -/
def canonicalPowerSubalgebra : Subalgebra ℂ (RootRing p τ) :=
  rootPowerSubalgebra p τ (signatureLcm p) (canonicalRootScale p a)
    (canonicalRoot_nat_denominator p hp ha τ hτ)

def canonicalPowerSubalgebraEquiv :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] canonicalPowerSubalgebra p hp ha τ hτ :=
  rootPowerSubalgebraEquiv p hp ha τ hτ (signatureLcm p) (canonicalRootScale p a)
    (canonicalRootScale_pos p hp ha τ hτ) (canonicalRoot_nat_denominator p hp ha τ hτ)

/-- Every admissible actual canonical root is finite free over the displayed polynomial subalgebra. -/
def canonicalRootFiniteFreeBasis :
    Module.Basis (RootBox p τ (canonicalRootScale p a))
      (canonicalPowerSubalgebra p hp ha τ hτ) (RootRing p τ) :=
  rootFiniteFreeBasis p hp ha τ hτ (signatureLcm p) (canonicalRootScale p a)
    (canonicalRootScale_pos p hp ha τ hτ) (canonicalRoot_nat_denominator p hp ha τ hτ)

theorem canonicalRoot_finite :
    Module.Finite (canonicalPowerSubalgebra p hp ha τ hτ) (RootRing p τ) :=
  Module.Finite.of_basis (canonicalRootFiniteFreeBasis p hp ha τ hτ)

theorem canonicalRoot_free :
    Module.Free (canonicalPowerSubalgebra p hp ha τ hτ) (RootRing p τ) :=
  Module.Free.of_basis (canonicalRootFiniteFreeBasis p hp ha τ hτ)

theorem canonicalRootFiniteFreeBasis_homogeneous (q : RootBox p τ (canonicalRootScale p a)) :
    canonicalRootFiniteFreeBasis p hp ha τ hτ q ∈
      rootPiece p τ (rootBoxDegree p τ (canonicalRootScale p a) q) :=
  rootFiniteFreeBasis_homogeneous p hp ha τ hτ (signatureLcm p) (canonicalRootScale p a)
    (canonicalRootScale_pos p hp ha τ hτ) (canonicalRoot_nat_denominator p hp ha τ hτ) q

include hp ha hτ in
theorem canonicalRootFiniteFreeBasis_degree_le (q : RootBox p τ (canonicalRootScale p a)) :
    rootBoxDegree p τ (canonicalRootScale p a) q ≤ a + n * signatureLcm p :=
  (rootBox_complement_degree p hp ha τ hτ (signatureLcm p) (canonicalRootScale p a) _
    (canonicalRoot_nat_denominator p hp ha τ hτ) q.val (rootBoxDegree_spec _ _ _ q)).1

include hp ha hτ in
theorem canonicalRoot_finiteType : Algebra.FiniteType ℂ (RootRing p τ) := by
  let A := canonicalPowerSubalgebra p hp ha τ hτ
  let : Module.Finite A (RootRing p τ) := canonicalRoot_finite p hp ha τ hτ
  have hA : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ))
      (canonicalPowerSubalgebraEquiv p hp ha τ hτ)
  exact Algebra.FiniteType.trans hA (inferInstance : Algebra.FiniteType A (RootRing p τ))

include hp ha hτ in
theorem canonicalRoot_noetherian : IsNoetherianRing (RootRing p τ) := by
  let : Algebra.FiniteType ℂ (RootRing p τ) := canonicalRoot_finiteType p hp ha τ hτ
  exact Algebra.FiniteType.isNoetherianRing ℂ (RootRing p τ)

end Canonical
end CanonicalRoots
