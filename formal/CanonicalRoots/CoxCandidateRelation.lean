import CanonicalRoots.CoxCandidateMonomials

noncomputable section
namespace CanonicalRoots.Cox

theorem exponents_nonneg (kind : Kind) (α β γ : ℤ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (i j : Fin 3) : 0 ≤ exponents kind α β γ i j := by
  cases kind <;> fin_cases i <;> fin_cases j <;> simp [exponents] <;> omega

theorem common_nonneg (kind : Kind) (α β γ : ℤ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (j : Fin 3) : 0 ≤ common kind α β γ j := by
  cases kind <;> fin_cases j <;> simp [common] <;> omega

end CanonicalRoots.Cox
namespace CanonicalRoots
open MvPolynomial

def candidateRelationExponent (e : TernaryCandidate) (i : Fin 3) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (Cox.exponents e.kind e.alpha e.beta e.gamma i j).toNat)

def candidateCommonExponent (e : TernaryCandidate) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (Cox.common e.kind e.alpha e.beta e.gamma j).toNat)

def candidateRelation (e : TernaryCandidate) : MvPolynomial (Fin 3) ℂ :=
  ∑ i, monomial (candidateRelationExponent e i) 1

theorem candidateRelationExponent_cast {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (i j : Fin 3) : (candidateRelationExponent e i j : ℤ) = Cox.exponents e.kind e.alpha e.beta e.gamma i j := by
  apply Int.toNat_of_nonneg
  exact Cox.exponents_nonneg e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) i j

theorem candidateCommonExponent_cast {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (j : Fin 3) : (candidateCommonExponent e j : ℤ) = Cox.common e.kind e.alpha e.beta e.gamma j := by
  apply Int.toNat_of_nonneg
  exact Cox.common_nonneg e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) j

/-- The integer substitution certificate gives an equality of actual monomial exponents. -/
theorem candidate_exponent_substitution {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (i : Fin 3) :
    ∑ l, candidateRelationExponent e i l • candidateMonomialExponent e l =
      Finsupp.single i (candidateSignature e i) + candidateCommonExponent e := by
  ext j
  simp only [Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply, Finsupp.single_apply]
  have h := Cox.substitution e.kind e.alpha e.beta e.gamma i j
  have hc : (∑ l, (candidateRelationExponent e i l : ℤ) * (candidateMonomialExponent e l j : ℤ)) =
      (if i = j then (candidateSignature e i : ℤ) else 0) + (candidateCommonExponent e j : ℤ) := by
    simp only [candidateRelationExponent_cast he, candidateMonomialExponent_cast he,
      candidateCommonExponent_cast he, candidateSignature_cast he]
    simpa only [eq_comm] using h
  exact_mod_cast hc

/-- Polynomial substitution by monomials, with no quotient or injectivity assumption. -/
theorem aeval_monomial_one_matrix (d : Fin 3 →₀ ℕ) (b : Fin 3 → Fin 3 →₀ ℕ) :
    aeval (fun i => (monomial (b i) 1 : MvPolynomial (Fin 3) ℂ)) (monomial d (1 : ℂ)) =
      monomial (∑ i, d i • b i) 1 := by
  rw [aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [monomial_pow, one_pow]
  exact (monomial_sum_one _ _).symm

/-- The Cox relation becomes the common monomial times the actual Fermat relation. -/
theorem candidate_relation_substitution {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    aeval (candidateMonomial e) (candidateRelation e) =
      monomial (candidateCommonExponent e) 1 * fermat (candidateSignature e) := by
  have hm : aeval (candidateMonomial e) (candidateRelation e) =
      ∑ i, monomial (∑ j, candidateRelationExponent e i j • candidateMonomialExponent e j) 1 := by
    simp only [candidateRelation, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact aeval_monomial_one_matrix (candidateRelationExponent e i) (candidateMonomialExponent e)
  rw [hm]
  simp_rw [candidate_exponent_substitution he]
  rw [fermat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [X_pow_eq_monomial, monomial_mul]
  simp only [mul_one, add_comm]

end CanonicalRoots
