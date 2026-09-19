import CanonicalRoots.RootBoxCardinality
import CanonicalRoots.HypersurfaceMultiplicity

noncomputable section
namespace CanonicalRoots

/-- The rational degree of an actual canonical root is determined by its root equation. -/
theorem root_rationalDegree_eq {n a : ℕ} (p : Fin n → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    rationalDegree p (fun i => ne_of_gt (lt_of_lt_of_le (by decide) (hp.1 i))) τ =
      (1 - ∑ i, (1 : ℚ) / p i) / a := by
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  apply (eq_div_iff ha0).mpr
  have he := congrArg
    (rationalDegree p (fun i => ne_of_gt (lt_of_lt_of_le (by decide) (hp.1 i)))) hτ
  simpa only [map_nsmul, nsmul_eq_mul, rationalDegree_omega, mul_comm] using he

namespace RootHypersurfacePresentation

/-- The multiplicity identity is forced by the actual root ring and its graded presentation. -/
theorem relationDegree_div_prod_weights {n a : ℕ} (p : Fin (n + 2) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (P : RootHypersurfacePresentation p τ) :
    (P.relationDegree : ℚ) / (∏ i, (P.weights i : ℚ)) =
      rationalDegree p (fun i => ne_of_gt (lt_of_lt_of_le (by decide) (hp.1 i))) τ ^ n := by
  let N := signatureLcm p
  let u := canonicalRootScale p a
  let μ := rationalDegree p (fun i => ne_of_gt (lt_of_lt_of_le (by decide) (hp.1 i))) τ
  have hNpos : 0 < N := signature_lcm_pos p (fun i => lt_of_lt_of_le (by decide) (hp.1 i))
  have hNzero : (N : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  have hWzero : (∏ i, (P.weights i : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast ne_of_gt (P.weights_pos i)
  have he := P.box_card_mul_weights p hp ha τ hτ N u
    (canonicalRootScale_pos p hp ha τ hτ) (canonicalRoot_nat_denominator p hp ha τ hτ) hNpos
  rw [canonicalRootBox_card p hp ha τ hτ] at he
  have heq : (N : ℚ) * (u : ℚ) ^ n * ∏ i, (P.weights i : ℚ) =
      (P.relationDegree : ℚ) * (N : ℚ) ^ (n + 1) := by exact_mod_cast he
  have huq : (u : ℚ) = (N : ℚ) * μ := canonicalRootScale_eq_lcm_mul_degree p hp ha τ hτ
  rw [huq] at heq
  have hcancel : (μ ^ n * ∏ i, (P.weights i : ℚ)) * (N : ℚ) ^ (n + 1) =
      (P.relationDegree : ℚ) * (N : ℚ) ^ (n + 1) := by
    calc
      _ = (N : ℚ) * ((N : ℚ) * μ) ^ n * ∏ i, (P.weights i : ℚ) := by
        rw [mul_pow, pow_succ]
        ring
      _ = _ := heq
  exact (div_eq_iff hWzero).mpr (mul_right_cancel₀ (pow_ne_zero _ hNzero) hcancel).symm

theorem relationDegree_div_prod_weights_explicit {n a : ℕ} (p : Fin (n + 2) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (P : RootHypersurfacePresentation p τ) :
    (P.relationDegree : ℚ) / (∏ i, (P.weights i : ℚ)) =
      ((1 - ∑ i, (1 : ℚ) / p i) / a) ^ n := by
  rw [P.relationDegree_div_prod_weights p hp ha τ hτ, root_rationalDegree_eq p hp ha τ hτ]

end RootHypersurfacePresentation

namespace Target

theorem relationDegree_div_prod_weights {r a : ℕ} (T : Target r a) :
    (T.presentation.relationDegree : ℚ) / (∏ i, (T.presentation.weights i : ℚ)) =
      ((1 - ∑ i, (1 : ℚ) / T.signature i) / a) ^ (r - 2) := by
  cases r with
  | zero => have h := T.dimension_input; omega
  | succ r =>
    cases r with
    | zero => have h := T.dimension_input; omega
    | succ r =>
      rw [show r + 1 + 1 - 2 = r by omega]
      exact T.presentation.relationDegree_div_prod_weights_explicit T.signature T.admissible
        T.parameter_input T.tau T.root_equation

/-- All three numerical necessary conditions, derived from the independent target semantics. -/
theorem numerical_identities {r a : ℕ} (T : Target r a) :
    T.presentation.relationDegree = a + ∑ i, T.presentation.weights i ∧
    (T.presentation.relationDegree : ℚ) / (∏ i, (T.presentation.weights i : ℚ)) =
      ((1 - ∑ i, (1 : ℚ) / T.signature i) / a) ^ (r - 2) ∧
    Finset.univ.gcd T.presentation.weights = 1 :=
  ⟨T.relationDegree_eq_add_sum_weights, T.relationDegree_div_prod_weights, T.weights_gcd_eq_one⟩

end Target
end CanonicalRoots
