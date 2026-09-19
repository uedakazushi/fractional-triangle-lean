import CanonicalRoots.RootHilbertSeries
import Mathlib.RingTheory.LaurentSeries

noncomputable section
namespace CanonicalRoots
open scoped RatFunc

local instance {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    Fintype (RootBox p τ u) := Fintype.ofFinite _

/-- Evaluation of the finite polynomial that supplies the Hilbert numerator. -/
def rootBoxValue {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ)
    {K : Type*} [CommSemiring K] (t : K) : K :=
  ∑ q : RootBox p τ u, t ^ rootBoxDegree p τ u q

theorem rootBoxValue_map {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ)
    {K L : Type*} [CommSemiring K] [CommSemiring L] (f : K →+* L) (t : K) :
    f (rootBoxValue p τ u t) = rootBoxValue p τ u (f t) := by
  simp [rootBoxValue, map_sum, map_pow]

def rootHilbertRationalValue {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) {K : Type*} [Field K] (t : K) : K :=
  rootBoxValue p τ u t / (1 - t ^ N) ^ n

def rootHilbertRational {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) : RatFunc ℚ := rootHilbertRationalValue p τ N u RatFunc.X

section Root
variable {n a : ℕ} (p : Fin (n + 1) → ℕ)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (N u : ℕ) (hN : N • τ = u • cDegree p)

include hp ha hτ hN in
theorem rootBoxValue_reciprocal {K : Type*} [Field K] (t : K) (ht : t ≠ 0) :
    t ^ (a + n * N) * rootBoxValue p τ u t⁻¹ = rootBoxValue p τ u t := by
  classical
  unfold rootBoxValue
  rw [Finset.mul_sum]
  calc
    _ = ∑ q : RootBox p τ u,
        t ^ rootBoxDegree p τ u (rootBoxComplement p hp ha τ hτ N u hN q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [rootBoxDegree_complement p hp ha τ hτ N u hN q, inv_pow,
        ← pow_sub₀ t ht
          (rootBox_complement_degree p hp ha τ hτ N u _ hN q.val
            (rootBoxDegree_spec p τ u q)).1]
    _ = _ := (rootBoxComplement p hp ha τ hτ N u hN).sum_comp
      (fun q => t ^ rootBoxDegree p τ u q)

include hp ha hτ hN in
/-- Reciprocity of the rational expression, using field division. -/
theorem rootHilbertRationalValue_reciprocal {K : Type*} [Field K] (t : K) (ht : t ≠ 0) :
    t ^ a * rootHilbertRationalValue p τ N u t⁻¹ =
      (-1) ^ n * rootHilbertRationalValue p τ N u t := by
  have hd : 1 - (t⁻¹) ^ N = -(1 - t ^ N) / t ^ N := by
    rw [inv_pow]
    field_simp
    ring
  unfold rootHilbertRationalValue
  calc
    _ = (-1) ^ n * (t ^ (a + n * N) * rootBoxValue p τ u t⁻¹) /
        (1 - t ^ N) ^ n := by
      rw [hd, div_pow, neg_pow, Nat.mul_comm n N]
      simp only [div_eq_mul_inv,
        mul_inv_rev, inv_inv, ← inv_pow, inv_neg, inv_one, pow_add, pow_mul]
      ring
    _ = _ := by rw [rootBoxValue_reciprocal p hp ha τ hτ N u hN t ht]; ring

include hp ha hτ hN in
/-- The displayed rational function represents the actual Hilbert series in Laurent series. -/
theorem rootHilbertSeries_eq_rational (hu : 0 < u) (hNpos : 0 < N) :
    (rootHilbertSeries p τ : LaurentSeries ℚ) =
      (rootHilbertRational p τ N u : LaurentSeries ℚ) := by
  have hd : (1 - (PowerSeries.X : PowerSeries ℚ) ^ N) ^ n ≠ 0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    simp [ne_of_gt hNpos] at hh
  have hdl : HahnSeries.ofPowerSeries ℤ ℚ ((1 - (PowerSeries.X : PowerSeries ℚ) ^ N) ^ n) ≠ 0 := by
    intro h
    apply hd
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using h
  have heq := congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
    (rootHilbertSeries_mul_denominator p hp ha τ hτ N u hu hN hNpos)
  simp only [map_mul, map_pow, map_sub, map_one] at heq hdl
  unfold rootHilbertRational rootHilbertRationalValue
  change _ = (algebraMap (RatFunc ℚ) (LaurentSeries ℚ))
    (rootBoxValue p τ u RatFunc.X / (1 - RatFunc.X ^ N) ^ n)
  simp only [map_div₀, map_pow, map_sub, map_one, rootBoxValue_map]
  rw [RatFunc.coe_X, ← PowerSeries.coe_X]
  apply (eq_div_iff hdl).mpr
  simpa only [rootBoxNumerator, rootBoxValue, map_sum, map_pow] using heq

end Root

/-- Canonical parameters discharge the denominator and scale hypotheses internally. -/
theorem canonicalRootHilbertSeries_eq_rational {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    (rootHilbertSeries p τ : LaurentSeries ℚ) =
      (rootHilbertRational p τ (signatureLcm p) (canonicalRootScale p a) : LaurentSeries ℚ) :=
  rootHilbertSeries_eq_rational p hp ha τ hτ (signatureLcm p) (canonicalRootScale p a)
    (canonicalRoot_nat_denominator p hp ha τ hτ) (canonicalRootScale_pos p hp ha τ hτ)
    (signature_lcm_pos p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)))

/-- The reciprocity identity in the rational function field, for every actual canonical root. -/
theorem canonicalRootHilbertRational_reciprocal {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    (RatFunc.X : RatFunc ℚ) ^ a *
      rootHilbertRationalValue p τ (signatureLcm p) (canonicalRootScale p a) RatFunc.X⁻¹ =
      (-1) ^ n * rootHilbertRational p τ (signatureLcm p) (canonicalRootScale p a) :=
  rootHilbertRationalValue_reciprocal p hp ha τ hτ (signatureLcm p) (canonicalRootScale p a)
    (canonicalRoot_nat_denominator p hp ha τ hτ) RatFunc.X RatFunc.X_ne_zero

end CanonicalRoots
