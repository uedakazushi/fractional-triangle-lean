import CanonicalRoots.CoxExplicitPolynomials
import CanonicalRoots.CoxCandidateHomogeneous

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- An invertible exponent matrix makes each term vanish at every critical point. -/
theorem candidate_gradient_terms_zero {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (z : Fin 3 → ℂ)
    (hz : ∀ i, eval z (pderiv i (candidateRelation e)) = 0) (i : Fin 3) :
    eval z (monomial (candidateRelationExponent e i) 1) = 0 := by
  let E : Matrix (Fin 3) (Fin 3) ℂ := (Cox.exponents e.kind e.alpha e.beta e.gamma).map Int.cast
  have hdet : E.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    change ((Cox.exponents e.kind e.alpha e.beta e.gamma).map (fun x => (x : ℂ))).det ≠ 0
    rw [← Int.cast_det, Cox.determinant]
    exact_mod_cast ne_of_gt (Cox.degree_pos e.kind e.alpha e.beta e.gamma
      (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1))
  have hcast (j k : Fin 3) : E j k = (candidateRelationExponent e j k : ℂ) := by
    change ((Cox.exponents e.kind e.alpha e.beta e.gamma j k : ℤ) : ℂ) = _
    rw [← candidateRelationExponent_cast he j k]
    simp
  have hv : (fun j => eval z (monomial (candidateRelationExponent e j) 1)) = 0 := by
    apply Matrix.mulVec_injective_of_det_ne_zero hdet
    rw [Matrix.mulVec_zero]
    ext k
    have hpoly : ∑ j, candidateRelationExponent e j k • monomial (candidateRelationExponent e j) (1 : ℂ) =
        X k * pderiv k (candidateRelation e) := by
      simp only [candidateRelation, map_sum, Finset.mul_sum, X_mul_pderiv_monomial]
    have hh := congrArg (eval z) hpoly
    simpa only [map_sum, map_nsmul, nsmul_eq_mul, map_mul, map_natCast, eval_X, hz, mul_zero,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, hcast, Pi.zero_apply] using hh
  exact congrFun hv i

end CanonicalRoots
