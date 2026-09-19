import CanonicalRoots.RootBoxPolynomial
import CanonicalRoots.WeightedHypersurfaceHilbert

noncomputable section
namespace CanonicalRoots

theorem one_sub_X_pow_ne_zero (k : ℕ) (hk : 0 < k) :
    (1 - Polynomial.X ^ k : Polynomial ℚ) ≠ 0 := by
  intro he
  have hc := congrArg (fun f : Polynomial ℚ => f.coeff 0) he
  simpa [ne_of_gt hk, Ne.symm (ne_of_gt hk)] using hc

theorem one_sub_X_pow_natDegree (k : ℕ) :
    (1 - Polynomial.X ^ k : Polynomial ℚ).natDegree = k := by
  have he : (1 - Polynomial.X ^ k : Polynomial ℚ) = -(Polynomial.X ^ k - 1) := by ring
  rw [he, Polynomial.natDegree_neg]
  simpa only [Polynomial.C_1] using
    (Polynomial.natDegree_X_pow_sub_C (R := ℚ) (n := k) (r := 1))

theorem weightedDenominator_ne_zero {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    (∏ i, (1 - Polynomial.X ^ w i : Polynomial ℚ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => one_sub_X_pow_ne_zero (w i) (hw i))

theorem weightedDenominator_natDegree {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    (∏ i, (1 - Polynomial.X ^ w i : Polynomial ℚ)).natDegree = ∑ i, w i := by
  rw [Polynomial.natDegree_prod _ _ (fun i _ => one_sub_X_pow_ne_zero (w i) (hw i))]
  simp only [one_sub_X_pow_natDegree]

namespace RootHypersurfacePresentation
section Root
variable {n a : ℕ} (p : Fin (n + 1) → ℕ)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (P : RootHypersurfacePresentation p τ)
  (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p) (hNpos : 0 < N)

include hp ha hτ hu hN hNpos in
/-- Comparing the two actual Hilbert series gives a polynomial identity. -/
theorem hilbert_polynomial_identity :
    rootBoxPolynomial p τ u * ∏ i, (1 - Polynomial.X ^ P.weights i) =
      (1 - Polynomial.X ^ P.relationDegree) * (1 - Polynomial.X ^ N) ^ n := by
  apply Polynomial.coe_injective ℚ
  change Polynomial.coeToPowerSeries.ringHom
      (rootBoxPolynomial p τ u * ∏ i, (1 - Polynomial.X ^ P.weights i)) =
    Polynomial.coeToPowerSeries.ringHom
      ((1 - Polynomial.X ^ P.relationDegree) * (1 - Polynomial.X ^ N) ^ n)
  simp only [map_mul, map_prod, map_sub, map_one, map_pow,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, rootBoxPolynomial_coe]
  rw [← rootHilbertSeries_mul_denominator p hp ha τ hτ N u hu hN hNpos,
    ← P.hilbertSeries_mul_denominator p τ]
  ring

include hp ha hτ hu hN hNpos in
theorem relationDegree_eq_add_sum_weights_of_denominator :
    P.relationDegree = a + ∑ i, P.weights i := by
  have he := congrArg Polynomial.natDegree (P.hilbert_polynomial_identity p hp ha τ hτ
    N u hu hN hNpos)
  rw [Polynomial.natDegree_mul
      (rootBoxPolynomial_ne_zero p hp ha τ hτ N u hu hN hNpos)
      (weightedDenominator_ne_zero P.weights P.weights_pos),
    Polynomial.natDegree_mul (one_sub_X_pow_ne_zero P.relationDegree P.relationDegree_pos)
      (pow_ne_zero n (one_sub_X_pow_ne_zero N hNpos)),
    rootBoxPolynomial_natDegree p hp ha τ hτ N u hu hN hNpos,
    weightedDenominator_natDegree P.weights P.weights_pos,
    Polynomial.natDegree_pow, one_sub_X_pow_natDegree, one_sub_X_pow_natDegree] at he
  omega

end Root

/-- The canonical parameter is forced by the actual root equation and graded presentation. -/
theorem relationDegree_eq_add_sum_weights {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (P : RootHypersurfacePresentation p τ) :
    P.relationDegree = a + ∑ i, P.weights i :=
  P.relationDegree_eq_add_sum_weights_of_denominator p hp ha τ hτ
    (signatureLcm p) (canonicalRootScale p a) (canonicalRootScale_pos p hp ha τ hτ)
    (canonicalRoot_nat_denominator p hp ha τ hτ)
    (signature_lcm_pos p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)))

end RootHypersurfacePresentation

namespace Target

/-- Every independently defined target satisfies the numerical parameter identity. -/
theorem relationDegree_eq_add_sum_weights {r a : ℕ} (T : Target r a) :
    T.presentation.relationDegree = a + ∑ i, T.presentation.weights i := by
  cases r with
  | zero => have h := T.dimension_input; omega
  | succ r =>
    exact T.presentation.relationDegree_eq_add_sum_weights T.signature
      T.admissible T.parameter_input T.tau T.root_equation

/-- Primitivity is a consequence of the target semantics, not a field of Target. -/
theorem weights_gcd_eq_one {r a : ℕ} (T : Target r a) :
    Finset.univ.gcd T.presentation.weights = 1 := by
  cases r with
  | zero => have h := T.dimension_input; omega
  | succ r =>
    exact T.presentation.weights_gcd_eq_one (by have h := T.dimension_input; omega)
      T.signature T.admissible T.parameter_input T.tau T.root_equation

end Target
end CanonicalRoots
