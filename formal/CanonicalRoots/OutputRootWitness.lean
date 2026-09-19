import CanonicalRoots.OutputClassification
import CanonicalRoots.RootWitnessSemantics

noncomputable section
namespace CanonicalRoots

theorem ternaryEquation_orderedSignature {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    (ternaryEquation a e).orderedSignature = List.ofFn (fun i => (candidateSignature e i : ℤ)) := by
  change (List.finRange 3).map (Cox.signature e.kind e.alpha e.beta e.gamma) = _
  rw [List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  exact (candidateSignature_cast he i).symm

theorem output_realization_with_signature {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ∃ t : Target ((enumerateCandidateEquations n a).get i).n a,
      t.presentation.polynomial = ((enumerateCandidateEquations n a).get i).polynomial ∧
      t.presentation.weights = ((enumerateCandidateEquations n a).get i).natWeights ∧
      (t.presentation.relationDegree : ℤ) = ((enumerateCandidateEquations n a).get i).relationDegree ∧
      ((enumerateCandidateEquations n a).get i).orderedSignature =
        List.ofFn (fun j => (t.signature j : ℤ)) := by
  by_cases hn3 : n = 3
  · subst n
    rw [ternary_output_get]
    have he := ternaryRepresentative_arithmetic ha (ternaryOutputIndex a i)
    obtain ⟨t,hp,hw,hd,hf⟩ := ternaryEquation_realization ha he
    refine ⟨t,hf,hw,hd,?_⟩
    rw [hp]
    exact ternaryEquation_orderedSignature he
  · rw [higher_output_get n a hn3]
    obtain ⟨t,hp,hw,hd,hf⟩ := higherEquation_realization_of_mem hn ha _
      (List.get_mem _ (higherOutputIndex n a hn3 i))
    refine ⟨t,hf,hw,hd,?_⟩
    change ((enumerateHigherCandidates n a).get (higherOutputIndex n a hn3 i)).map Int.ofNat = _
    exact (congrArg (List.map Int.ofNat) hp).symm.trans (by rw [List.map_ofFn]; rfl)

/-- Each serialized root witness is the actual root of the same target realizing the equation. -/
theorem output_root_witness {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ∃ t : Target ((enumerateCandidateEquations n a).get i).n a,
      t.presentation.polynomial = ((enumerateCandidateEquations n a).get i).polynomial ∧
      t.presentation.weights = ((enumerateCandidateEquations n a).get i).natWeights ∧
      (t.presentation.relationDegree : ℤ) = ((enumerateCandidateEquations n a).get i).relationDegree ∧
      ((enumerateCandidateEquations n a).get i).orderedSignature =
        List.ofFn (fun j => (t.signature j : ℤ)) ∧
      rootWitnessDegree a t.signature = t.tau := by
  obtain ⟨t,hf,hw,hd,hp⟩ := output_realization_with_signature hn ha i
  exact ⟨t,hf,hw,hd,hp,rootWitnessDegree_eq t.signature
    (fun j => lt_of_lt_of_le (by decide) (t.admissible.1 j)) ha t.tau t.root_equation⟩

end CanonicalRoots
