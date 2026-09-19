import CanonicalRoots.HigherSemanticEnumeration

noncomputable section
open CanonicalRoots

-- Every row, not merely the selected regression rows, is a signature of an actual Target.
example (ps : List ℕ) (h : ps ∈ enumerateHigherCandidates 4 1) :
    ∃ t : Target 4 1, List.ofFn t.signature = ps :=
  enumerateHigherCandidates_target_sound (by decide) (by decide) ps h

-- An unsorted actual signature is represented by an enumerated graded Fermat model.
example : ∃ t : Target 4 25, t.signature = ![67,2,7,3] ∧
    ∃ p : Fin 4 → ℕ, List.ofFn p ∈ enumerateHigherCandidates 4 25 ∧
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (fermat p) (productWeights p))) := by
  obtain ⟨t, ht⟩ := (higher_signature_target_iff ![67,2,7,3] (by decide)
    (by decide +kernel) (by decide : 1 ≤ 25)).mpr
    ⟨by unfold Pairwise; decide +kernel, by decide +kernel⟩
  exact ⟨t, ht, t.higher_enumerated_graded_model (by decide)⟩

-- The tuple-to-list bridge keeps inadmissible inputs excluded without a positivity premise.
example : List.ofFn (![0,3,7,43] : Fin 4 → ℕ) ∉ enumerateHigherCandidates 4 1 := by
  intro hm
  obtain ⟨_, t, ht⟩ := (higher_sorted_signature_enumerated_iff ![0,3,7,43]
    (by decide) (by decide : 1 ≤ 1)).mp hm
  have hp := t.admissible.1 0
  rw [ht] at hp
  norm_num at hp

end
