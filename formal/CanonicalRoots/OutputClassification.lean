import CanonicalRoots.TernaryOutputClassification
import CanonicalRoots.HigherOutputClassification
import CanonicalRoots.MinimalGenerators

noncomputable section
namespace CanonicalRoots

theorem output_dimensions {n a : ℕ} (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ((enumerateCandidateEquations n a).get i).n = n ∧
      ((enumerateCandidateEquations n a).get i).a = a := by
  by_cases hn : n = 3
  · subst n
    rw [ternary_output_get]
    exact ⟨rfl,rfl⟩
  · rw [higher_output_get n a hn]
    exact ⟨((enumerateHigherCandidates_iff n a ha _).mp (List.get_mem _ _)).1,rfl⟩

/-- Every actual output presentation realizes an independently defined target. -/
theorem output_realization {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ∃ t : Target ((enumerateCandidateEquations n a).get i).n a,
      t.presentation.polynomial = ((enumerateCandidateEquations n a).get i).polynomial ∧
      t.presentation.weights = ((enumerateCandidateEquations n a).get i).natWeights ∧
      (t.presentation.relationDegree : ℤ) = ((enumerateCandidateEquations n a).get i).relationDegree := by
  by_cases h : n = 3
  · subst n
    exact ternary_output_sound ha i
  · exact higher_output_sound (by omega) ha i

theorem output_pairwise_nonisomorphic {n a : ℕ} (ha : 1 ≤ a)
    (i j : Fin (enumerateCandidateEquations n a).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv ((enumerateCandidateEquations n a).get i).piece
      ((enumerateCandidateEquations n a).get j).piece) := by
  by_cases h : n = 3
  · subst n
    exact ternary_output_pairwise_nonisomorphic ha i j hij
  · exact higher_output_pairwise_nonisomorphic h ha i j hij

/-- Completeness quantifies over actual roots and arbitrary isolated presentations. -/
theorem Target.output_complete_unique {n a : ℕ} (t : Target n a) :
    ∃! i : Fin (enumerateCandidateEquations n a).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        ((enumerateCandidateEquations n a).get i).piece) := by
  by_cases h : n = 3
  · subst n
    exact t.ternary_output_complete_unique
  · cases n with
    | zero => have ht := t.dimension_input; omega
    | succ n =>
      exact t.higher_output_complete_unique (by have ht := t.dimension_input; omega)

theorem output_isolated {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    IsolatedAtOrigin ((enumerateCandidateEquations n a).get i).polynomial := by
  obtain ⟨t,hf,_,_⟩ := output_realization hn ha i
  rw [← hf]
  exact t.presentation.isolated

theorem output_noConstantOrLinear {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    HasNoConstantOrLinear ((enumerateCandidateEquations n a).get i).polynomial := by
  obtain ⟨t,hf,_,_⟩ := output_realization hn ha i
  rw [← hf]
  exact t.presentation.no_constant_or_linear

theorem output_minimum_generators {n a m : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length)
    (q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ((enumerateCandidateEquations n a).get i).Ring)
    (hq : Function.Surjective q) : n ≤ m := by
  rw [← (output_dimensions ha i).1]
  exact presented_minimum_generators _ (output_noConstantOrLinear hn ha i) q hq

theorem output_parameter {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ((enumerateCandidateEquations n a).get i).relationDegree =
      a + ∑ j, (((enumerateCandidateEquations n a).get i).natWeights j : ℤ) := by
  obtain ⟨t,_,hw,hd⟩ := output_realization hn ha i
  rw [← hd, ← hw]
  exact_mod_cast t.relationDegree_eq_add_sum_weights

end CanonicalRoots
