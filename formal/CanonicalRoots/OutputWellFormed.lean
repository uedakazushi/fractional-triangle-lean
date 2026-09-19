import CanonicalRoots.OutputRootWitness

noncomputable section
namespace CanonicalRoots

theorem ternaryEquation_weights_exact {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    (ternaryEquation a e).weights = List.ofFn (fun i => ((ternaryEquation a e).natWeights i : ℤ)) := by
  rw [ternaryEquation_weights, ternaryEquation_natWeights]
  congr 1
  funext i
  exact (candidateNatWeights_cast he _).symm

theorem higherEquation_weights_exact (a : ℕ) (ps : List ℕ) (hp : ∀ i, 0 < ps.get i) :
    (higherEquation a ps).weights = List.ofFn (fun i => ((higherEquation a ps).natWeights i : ℤ)) := by
  rw [higherEquation_weights, higherEquation_natWeights a ps hp,
    higherCoordinateWeight_eq_productWeights ps.get hp]
  rfl

theorem output_weights_exact {n a : ℕ} (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ((enumerateCandidateEquations n a).get i).weights =
      List.ofFn (fun j => (((enumerateCandidateEquations n a).get i).natWeights j : ℤ)) := by
  by_cases hn : n = 3
  · subst n
    rw [ternary_output_get]
    exact ternaryEquation_weights_exact (ternaryRepresentative_arithmetic ha _)
  · rw [higher_output_get n a hn]
    apply higherEquation_weights_exact
    intro j
    have hA := (enumerateHigherCandidates_iff n a ha _).mp
      (List.get_mem _ (higherOutputIndex n a hn i))
    exact lt_of_lt_of_le (by decide) (hA.2.1 _ (List.get_mem _ j))

theorem output_weights_length {n a : ℕ} (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ((enumerateCandidateEquations n a).get i).weights.length = n := by
  rw [output_weights_exact ha i, List.length_ofFn, (output_dimensions ha i).1]

theorem output_weights_positive {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ∀ w ∈ ((enumerateCandidateEquations n a).get i).weights, 0 < w := by
  rw [output_weights_exact ha i]
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
  obtain ⟨t,_,hw,_⟩ := output_realization hn ha i
  rw [← hw]
  exact_mod_cast t.presentation.weights_pos j

theorem output_weights_primitive {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    Finset.univ.gcd ((enumerateCandidateEquations n a).get i).natWeights = 1 := by
  obtain ⟨t,_,hw,_⟩ := output_realization hn ha i
  rw [← hw]
  exact t.weights_gcd_eq_one

theorem output_weights_sorted {n a : ℕ} (i : Fin (enumerateCandidateEquations n a).length) :
    ((enumerateCandidateEquations n a).get i).weights.SortedLE := by
  by_cases hn : n = 3
  · subst n
    rw [ternary_output_get, ternaryEquation_weights]
    exact List.sortedLE_ofFn_iff.mpr (displayVariablePermutation_sorted _)
  · rw [higher_output_get n a hn, higherEquation_weights]
    apply List.sortedLE_ofFn_iff.mpr
    exact displayVariablePermutation_sorted (higherCoordinateWeight
      ((enumerateHigherCandidates n a).get (higherOutputIndex n a hn i)).get)

theorem output_exponents_nonnegative {n a : ℕ} (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ∀ row ∈ ((enumerateCandidateEquations n a).get i).exponents,
      row.length = n ∧ ∀ x ∈ row, 0 ≤ x := by
  by_cases hn : n = 3
  · subst n
    rw [ternary_output_get]
    exact ternaryEquation_exponents_nonnegative (ternaryRepresentative_arithmetic ha _)
  · rw [higher_output_get n a hn]
    have hlen := ((enumerateHigherCandidates_iff n a ha _).mp
      (List.get_mem _ (higherOutputIndex n a hn i))).1
    simpa only [hlen] using higherEquation_exponents_nonnegative a
      ((enumerateHigherCandidates n a).get (higherOutputIndex n a hn i))

theorem output_exponents_length {n a : ℕ} (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ((enumerateCandidateEquations n a).get i).exponents.length = n := by
  by_cases hn : n = 3
  · subst n
    rw [ternary_output_get, ternaryEquation_exponents, List.length_ofFn]
  · rw [higher_output_get n a hn, higherEquation_exponents, List.length_ofFn]
    exact ((enumerateHigherCandidates_iff n a ha _).mp
      (List.get_mem _ (higherOutputIndex n a hn i))).1

end CanonicalRoots
