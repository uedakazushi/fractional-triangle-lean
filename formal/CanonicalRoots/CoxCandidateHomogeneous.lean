import CanonicalRoots.CoxCandidateMap

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def candidateNatDegree (e : TernaryCandidate) : ℕ := (candidateDegree e).toNat

theorem candidateNatDegree_cast {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    (candidateNatDegree e : ℤ) = candidateDegree e :=
  Int.toNat_of_nonneg (le_of_lt (Cox.degree_pos e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1)))

theorem candidateNatWeights_pos {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) (i : Fin 3) :
    0 < candidateNatWeights e i := by
  have hc := candidateNatWeights_cast he i
  have hp := Cox.weights_pos e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) i
  change 0 < candidateWeights e i at hp
  omega

theorem candidateNatDegree_pos {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    0 < candidateNatDegree e := by
  have hc := candidateNatDegree_cast he
  have hp := Cox.degree_pos e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1)
  change 0 < candidateDegree e at hp
  omega

theorem candidateRelation_homogeneous {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    IsWeightedHomogeneous (candidateNatWeights e) (candidateRelation e) (candidateNatDegree e) := by
  apply IsWeightedHomogeneous.sum
  intro i _
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_eq_sum]
  have hc : ∑ j, (candidateRelationExponent e i j : ℤ) * (candidateNatWeights e j : ℤ) =
      (candidateNatDegree e : ℤ) := by
    simp only [candidateRelationExponent_cast he, candidateNatWeights_cast he, candidateNatDegree_cast he]
    exact Cox.homogeneous e.kind e.alpha e.beta e.gamma i
  exact_mod_cast hc

theorem candidateNatDegree_eq_add_sum_weights {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : candidateNatDegree e = a + ∑ i, candidateNatWeights e i := by
  have hh := he.2.2.2.2
  change candidateDegree e - ∑ i, candidateWeights e i = (a : ℤ) at hh
  have hi : (candidateNatDegree e : ℤ) = (a : ℤ) + ∑ i, (candidateNatWeights e i : ℤ) := by
    simp only [candidateNatDegree_cast he, candidateNatWeights_cast he]
    linarith
  exact_mod_cast hi

theorem candidateRelation_ne_zero (e : TernaryCandidate) : candidateRelation e ≠ 0 := by
  intro hz
  have he := congrArg (eval (fun _ : Fin 3 => (1 : ℂ))) hz
  simp [candidateRelation, eval_monomial] at he

/-- Positive defect rules out constant and linear terms in a homogeneous polynomial. -/
theorem homogeneous_positive_defect_no_linear {n h : ℕ} (w : Fin n → ℕ) (f : MvPolynomial (Fin n) ℂ)
    (hf : IsWeightedHomogeneous w f h) (hdef : (∑ i, w i) < h) : HasNoConstantOrLinear f := by
  constructor
  · by_contra hn
    have he := hf hn
    simp only [map_zero] at he
    omega
  · intro i
    by_contra hn
    have he := hf hn
    simp only [Finsupp.weight_single, one_smul] at he
    have hi : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i)
    omega

theorem candidateRelation_no_constant_or_linear {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : HasNoConstantOrLinear (candidateRelation e) := by
  apply homogeneous_positive_defect_no_linear _ _ (candidateRelation_homogeneous he)
  rw [candidateNatDegree_eq_add_sum_weights he]
  omega

end CanonicalRoots
