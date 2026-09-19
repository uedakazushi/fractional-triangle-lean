import CanonicalRoots.DisplayVariableOrder
import CanonicalRoots.EquationSemantics
import CanonicalRoots.PresentedGradedRename
import CanonicalRoots.TernaryRealization

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem ternaryEquation_natWeights (a : ℕ) (e : TernaryCandidate) :
    (ternaryEquation a e).natWeights = candidateNatWeights e ∘ displayVariablePermutation (candidateWeights e) := by
  ext i
  change (((ternaryEquation a e).weights.getD i.val 0).toNat) =
    (candidateWeights e (displayVariablePermutation (candidateWeights e) i)).toNat
  rw [ternaryEquation_weights]
  have hi : i.val < 3 := i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_ofFn, Function.comp_apply]
  rfl

/-- The serialized exponent columns give precisely the renamed Cox polynomial. -/
theorem ternaryEquation_polynomial (a : ℕ) (e : TernaryCandidate) :
    (ternaryEquation a e).polynomial =
      rename (displayVariablePermutation (candidateWeights e)).symm (candidateRelation e) := by
  change ((ternaryEquation a e).exponents.map (fun row => monomial (equationExponent 3 row) 1)).sum = _
  rw [ternaryEquation_exponents, List.map_ofFn, List.sum_ofFn]
  simp only [candidateRelation, map_sum, rename_monomial, Function.comp_apply, equationExponent_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun d : Fin 3 →₀ ℕ => monomial d (1 : ℂ))
  ext j
  simp [candidateRelationExponent, Finsupp.mapDomain_equiv_apply]

def ternaryEquationGradedEquiv {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    GradedAlgEquiv (ternaryEquation a e).piece
      (rootPiece (candidateTarget ha he).signature (candidateTarget ha he).tau) := by
  have φ := (presentedGradedRename (candidateRelation e) (candidateNatWeights e)
    (displayVariablePermutation (candidateWeights e)).symm).symm.trans (candidateTargetGradedEquiv ha he)
  change GradedAlgEquiv (presentedPiece (ternaryEquation a e).polynomial (ternaryEquation a e).natWeights) _
  rw [ternaryEquation_polynomial, ternaryEquation_natWeights]
  exact φ

theorem ternaryEquation_polynomial_isolated {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : IsolatedAtOrigin (ternaryEquation a e).polynomial := by
  rw [ternaryEquation_polynomial]
  exact isolatedAtOrigin_rename _ (candidateRelation_isolated he) _

theorem ternaryEquation_polynomial_noConstantOrLinear {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : HasNoConstantOrLinear (ternaryEquation a e).polynomial := by
  rw [ternaryEquation_polynomial]
  exact noConstantOrLinear_rename _ (candidateRelation_no_constant_or_linear ha he) _

theorem ternaryEquation_polynomial_homogeneous {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    IsWeightedHomogeneous (ternaryEquation a e).natWeights (ternaryEquation a e).polynomial
      (candidateNatDegree e) := by
  rw [ternaryEquation_polynomial, ternaryEquation_natWeights]
  exact (homogeneous_rename_weights_iff (candidateNatWeights e)
    (displayVariablePermutation (candidateWeights e)).symm _ _).mpr (candidateRelation_homogeneous he)

theorem ternaryEquation_weights_positive {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : ∀ w ∈ (ternaryEquation a e).weights, 0 < w := by
  rw [ternaryEquation_weights]
  intro w hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  change 0 < candidateWeights e _
  rw [← candidateNatWeights_cast he]
  exact_mod_cast candidateNatWeights_pos he _

/-- The integer entries consumed by the polynomial interpretation are all genuine natural exponents. -/
theorem ternaryEquation_exponents_nonnegative {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    ∀ row ∈ (ternaryEquation a e).exponents, row.length = 3 ∧ ∀ x ∈ row, 0 ≤ x := by
  rw [ternaryEquation_exponents]
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  refine ⟨by simp,?_⟩
  intro x hx
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
  exact Cox.exponents_nonneg _ _ _ _ (by exact_mod_cast he.1)
    (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) _ _

theorem ternaryEquation_realization {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    ∃ t : Target 3 a, t.signature = candidateSignature e ∧
      t.presentation.weights = (ternaryEquation a e).natWeights ∧
      (t.presentation.relationDegree : ℤ) = (ternaryEquation a e).relationDegree ∧
      t.presentation.polynomial = (ternaryEquation a e).polynomial := by
  let s := candidateTarget ha he
  let H := s.presentation.renameGenerators (displayVariablePermutation (candidateWeights e)).symm
  let t : Target 3 a := { s with presentation := H }
  refine ⟨t,candidateTarget_signature ha he,?_,?_,?_⟩
  · change s.presentation.weights ∘ displayVariablePermutation (candidateWeights e) = _
    rw [show s.presentation.weights = candidateNatWeights e from candidateTarget_weights ha he,
      ternaryEquation_natWeights]
  · change ((candidateTarget ha he).presentation.relationDegree : ℤ) = candidateDegree e
    rw [candidateTarget_degree, candidateNatDegree_cast he]
  · change rename (displayVariablePermutation (candidateWeights e)).symm
      (candidateTarget ha he).presentation.polynomial = _
    rw [candidateTarget_polynomial, ternaryEquation_polynomial]

end CanonicalRoots
