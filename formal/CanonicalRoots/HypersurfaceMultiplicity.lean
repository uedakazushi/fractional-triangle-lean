import CanonicalRoots.HypersurfaceNumerics
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
namespace CanonicalRoots

/-- The factor left after cancelling the simple zero of 1-X^k at X=1. -/
def geometricPolynomial (k : ℕ) : Polynomial ℚ := ∑ i ∈ Finset.range k, Polynomial.X ^ i

theorem one_sub_X_pow_factor (k : ℕ) :
    (1 - Polynomial.X ^ k : Polynomial ℚ) = (1 - Polynomial.X) * geometricPolynomial k :=
  (mul_neg_geom_sum _ k).symm

theorem geometricPolynomial_eval_one (k : ℕ) : (geometricPolynomial k).eval 1 = k := by
  simp [geometricPolynomial]

theorem rootBoxPolynomial_eval_one {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    (rootBoxPolynomial p τ u).eval 1 = Nat.card (RootBox p τ u) := by
  classical
  let : Fintype (RootBox p τ u) := Fintype.ofFinite _
  change (Polynomial.evalRingHom 1) (rootBoxPolynomial p τ u) = _
  simp [rootBoxPolynomial, map_sum, Nat.card_eq_fintype_card]

theorem weightedDenominator_factor {n : ℕ} (w : Fin n → ℕ) :
    (∏ i, (1 - Polynomial.X ^ w i : Polynomial ℚ)) =
      (1 - Polynomial.X) ^ n * ∏ i, geometricPolynomial (w i) := by
  simp_rw [one_sub_X_pow_factor, Finset.prod_mul_distrib]
  simp

namespace RootHypersurfacePresentation

/-- The remaining multiplicity problem is an exact count of the root box. -/
theorem box_card_mul_weights {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (P : RootHypersurfacePresentation p τ)
    (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p) (hNpos : 0 < N) :
    Nat.card (RootBox p τ u) * ∏ i, P.weights i = P.relationDegree * N ^ n := by
  have he := P.hilbert_polynomial_identity p hp ha τ hτ N u hu hN hNpos
  rw [weightedDenominator_factor, one_sub_X_pow_factor P.relationDegree,
    one_sub_X_pow_factor N, mul_pow] at he
  have he' : (1 - Polynomial.X : Polynomial ℚ) ^ (n + 1) *
        (rootBoxPolynomial p τ u * ∏ i, geometricPolynomial (P.weights i)) =
      (1 - Polynomial.X : Polynomial ℚ) ^ (n + 1) *
        (geometricPolynomial P.relationDegree * geometricPolynomial N ^ n) := by
    calc
      _ = rootBoxPolynomial p τ u * ((1 - Polynomial.X) ^ (n + 1) *
          ∏ i, geometricPolynomial (P.weights i)) := by ring
      _ = _ := he
      _ = _ := by ring
  have hc : (1 - Polynomial.X : Polynomial ℚ) ^ (n + 1) ≠ 0 := by
    apply pow_ne_zero
    simpa using one_sub_X_pow_ne_zero 1 (by decide)
  have hcancel := mul_left_cancel₀ hc he'
  have hev := congrArg (Polynomial.eval 1) hcancel
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_pow,
    geometricPolynomial_eval_one, rootBoxPolynomial_eval_one] at hev
  exact_mod_cast hev

end RootHypersurfacePresentation
end CanonicalRoots
