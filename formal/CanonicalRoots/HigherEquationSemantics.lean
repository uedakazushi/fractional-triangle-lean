import CanonicalRoots.HigherDisplayData
import CanonicalRoots.EquationSemantics
import CanonicalRoots.PresentedGradedRename

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem higherEquation_weights (a : ℕ) (ps : List ℕ) :
    (higherEquation a ps).weights = List.ofFn (fun i =>
      higherCoordinateWeight ps.get (displayVariablePermutation (higherCoordinateWeight ps.get) i)) := by
  simpa only [List.ofFn_get] using higherEquation_weights_ofFn a ps.get

theorem higherEquation_exponents (a : ℕ) (ps : List ℕ) :
    (higherEquation a ps).exponents = List.ofFn (fun i => List.ofFn
      (fun j => if i = displayVariablePermutation (higherCoordinateWeight ps.get) j then (ps.get i : ℤ) else 0)) := by
  simpa only [List.ofFn_get] using higherEquation_exponents_ofFn a ps.get

theorem higherEquation_natWeights (a : ℕ) (ps : List ℕ) (hp : ∀ i, 0 < ps.get i) :
    (higherEquation a ps).natWeights = productWeights ps.get ∘
      displayVariablePermutation (higherCoordinateWeight ps.get) := by
  ext i
  change ((higherEquation a ps).weights.getD i.val 0).toNat = _
  rw [higherEquation_weights]
  have hi : i.val < ps.length := i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_ofFn, higherCoordinateWeight_eq_productWeights ps.get hp,
    Int.toNat_natCast, Function.comp_apply]
  rfl

/-- The displayed higher polynomial is the actual Fermat polynomial with its columns reordered. -/
theorem higherEquation_polynomial (a : ℕ) (ps : List ℕ) :
    (higherEquation a ps).polynomial =
      rename (displayVariablePermutation (higherCoordinateWeight ps.get)).symm (fermat ps.get) := by
  change ((higherEquation a ps).exponents.map (fun row => monomial (equationExponent ps.length row) 1)).sum = _
  rw [higherEquation_exponents, List.map_ofFn, List.sum_ofFn]
  simp only [fermat, map_sum, X_pow_eq_monomial, rename_monomial,
    Function.comp_apply, equationExponent_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun d : Fin ps.length →₀ ℕ => monomial d (1 : ℂ))
  ext j
  simp [Finsupp.mapDomain_equiv_apply, Finsupp.single_apply, Equiv.eq_symm_apply,
    Equiv.symm_apply_eq, apply_ite, eq_comm]
  split_ifs <;> simp_all

def higherEquationModelEquiv (a : ℕ) (ps : List ℕ) (hp : ∀ i, 0 < ps.get i) :
    GradedAlgEquiv (presentedPiece (fermat ps.get) (productWeights ps.get)) (higherEquation a ps).piece := by
  change GradedAlgEquiv _ (presentedPiece (higherEquation a ps).polynomial (higherEquation a ps).natWeights)
  rw [higherEquation_polynomial, higherEquation_natWeights a ps hp]
  exact presentedGradedRename _ _ (displayVariablePermutation (higherCoordinateWeight ps.get)).symm

theorem higherEquation_polynomial_isolated (a : ℕ) (ps : List ℕ) (hp : ∀ i, 2 ≤ ps.get i) :
    IsolatedAtOrigin (higherEquation a ps).polynomial := by
  rw [higherEquation_polynomial]
  exact isolatedAtOrigin_rename _ (fermat_isolated ps.get hp) _

theorem higherEquation_exponents_nonnegative (a : ℕ) (ps : List ℕ) :
    ∀ row ∈ (higherEquation a ps).exponents, row.length = ps.length ∧ ∀ x ∈ row, 0 ≤ x := by
  rw [higherEquation_exponents]
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  refine ⟨by simp,?_⟩
  intro x hx
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
  split_ifs <;> positivity

end CanonicalRoots
