import CanonicalRoots.RootBoxParameters
import CanonicalRoots.CanonicalFiniteFree

noncomputable section
namespace CanonicalRoots

theorem rootBoxParameters_card {n : ℕ} (p : Fin (n + 2) → ℕ)
    (b : ℤ) (σ : Fin (n + 2) → ℤ) (u : ℕ) (hu : 0 < u) :
    Nat.card (RootBoxParameters p b σ u) = signatureLcm p * u ^ n := by
  classical
  let (m : Fin (signatureLcm p)) : Finite (BoundedSumFiber (n + 1) u (rootCarry p b σ m)) :=
    inferInstanceAs (Finite {_d : Fin (n + 1) → Fin u // _})
  rw [RootBoxParameters, Nat.card_sigma]
  simp [boundedSumFiber_card n u hu]

/-- The exact cardinality is obtained by a bijection of finite sets, with no asymptotic premise. -/
theorem rootBox_card {n a : ℕ} (p : Fin (n + 2) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (u : ℕ) (hu : 0 < u) (hN : signatureLcm p • τ = u • cDegree p) :
    Nat.card (RootBox p τ u) = signatureLcm p * u ^ n := by
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  obtain ⟨b, σ, _hσ, rfl⟩ := degree_normal_exists p hpos τ
  rw [← Nat.card_congr (rootBoxParametersEquiv p hp ha b σ hτ u hN)]
  exact rootBoxParameters_card p b σ u hu

theorem canonicalRootBox_card {n a : ℕ} (p : Fin (n + 2) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    Nat.card (RootBox p τ (canonicalRootScale p a)) =
      signatureLcm p * canonicalRootScale p a ^ n :=
  rootBox_card p hp ha τ hτ (canonicalRootScale p a)
    (canonicalRootScale_pos p hp ha τ hτ) (canonicalRoot_nat_denominator p hp ha τ hτ)

/-- The free rank of the actual root ring over its actual polynomial subalgebra. -/
theorem canonicalRoot_finrank {n a : ℕ} (p : Fin (n + 2) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    Module.finrank (canonicalPowerSubalgebra p hp ha τ hτ) (RootRing p τ) =
      signatureLcm p * canonicalRootScale p a ^ n := by
  let : Nontrivial (canonicalPowerSubalgebra p hp ha τ hτ) :=
    (canonicalPowerSubalgebraEquiv p hp ha τ hτ).injective.nontrivial
  rw [Module.finrank_eq_nat_card_basis (canonicalRootFiniteFreeBasis p hp ha τ hτ)]
  exact canonicalRootBox_card p hp ha τ hτ

theorem canonicalRootScale_eq_lcm_mul_degree {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    (canonicalRootScale p a : ℚ) = (signatureLcm p : ℚ) *
      rationalDegree p (fun i => ne_of_gt (lt_of_lt_of_le (by decide) (hp.1 i))) τ := by
  have he := congrArg
    (rationalDegree p (fun i => ne_of_gt (lt_of_lt_of_le (by decide) (hp.1 i))))
    (canonicalRoot_nat_denominator p hp ha τ hτ)
  simpa only [canonicalRootScale, map_nsmul, nsmul_eq_mul, rationalDegree_c, mul_one] using he.symm

end CanonicalRoots
