import CanonicalRoots.HigherClassification

noncomputable section
open CanonicalRoots

-- Different actual Fermat models at the SAME root index are not graded-isomorphic.
example : ¬Nonempty (GradedAlgEquiv
    (presentedPiece (fermat (![2,3,7,61] : Fin 4 → ℕ)) (productWeights ![2,3,7,61]))
    (presentedPiece (fermat (![2,3,11,17] : Fin 4 → ℕ)) (productWeights ![2,3,11,17]))) := by
  apply enumerateHigherCandidates_models_nonisomorphic (by decide : 1 ≤ 19)
  · apply (enumerateHigherCandidates_ofFn_iff _ (by decide +kernel) (by decide)).mpr
    exact ⟨by decide +kernel, by decide +kernel,
      by unfold Pairwise; decide +kernel, by decide +kernel⟩
  · apply (enumerateHigherCandidates_ofFn_iff _ (by decide +kernel) (by decide)).mpr
    exact ⟨by decide +kernel, by decide +kernel,
      by unfold Pairwise; decide +kernel, by decide +kernel⟩
  · intro h
    have he := congrFun h 2
    norm_num at he

-- The number of output positions is finite and each Target has exactly one position.
example {n a : ℕ} (t : Target (n + 1) a) (hn : 3 ≤ n) :
    ∃! i : Fin (enumerateHigherCandidates (n + 1) a).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (fermat (higherCandidateSignature (n + 1) a t.parameter_input i))
          (productWeights (higherCandidateSignature (n + 1) a t.parameter_input i)))) :=
  t.higher_candidates_complete_unique hn

-- The general cotangent argument also distinguishes two gradings of a polynomial ring.
example : ¬Nonempty (GradedAlgEquiv
    (presentedPiece (0 : MvPolynomial (Fin 3) ℂ) (fun _ => 1))
    (presentedPiece (0 : MvPolynomial (Fin 3) ℂ) (fun _ => 2))) := by
  rintro ⟨e⟩
  obtain ⟨σ, hσ⟩ := gradedEquiv_weights_permutation 0 0
    (by simp [HasNoConstantOrLinear]) (by simp [HasNoConstantOrLinear])
    (fun _ => 1) (fun _ => 2) (by simp) e
  have := hσ 0
  norm_num at this

end
