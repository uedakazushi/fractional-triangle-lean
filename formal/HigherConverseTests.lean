import CanonicalRoots.HigherConverse

noncomputable section
open CanonicalRoots

private theorem admissible23767 : AdmissibleSignature ![2,3,7,67] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

-- This actual nonmaximal root exists, but cannot be an isolated hypersurface.
example : ∃ τ : DegreeGroup ![2,3,7,67], IsCanonicalRoot ![2,3,7,67] 5 τ ∧
    ¬Nonempty (RootHypersurfacePresentation ![2,3,7,67] τ) := by
  obtain ⟨τ, hτ⟩ := (canonicalRoot_exists_iff ![2,3,7,67] (by decide +kernel) (a := 5)).mpr
    (by decide +kernel)
  refine ⟨τ, hτ, ?_⟩
  rintro ⟨H⟩
  have he := H.higher_scale_eq_one ![2,3,7,67] admissible23767 (by decide) τ hτ (by decide)
  norm_num [show canonicalRootScale ![2,3,7,67] 5 = 5 from by decide +kernel] at he

-- At the maximal root index the same signature does give an actual Target.
example : ∃ t : Target 4 25, t.signature = ![2,3,7,67] := by
  apply (higher_signature_target_iff ![2,3,7,67] (by decide) (by decide +kernel) (by decide)).mpr
  exact ⟨by unfold Pairwise; decide +kernel, by decide +kernel⟩

example : ∃ t : Target 4 1, t.signature = ![2,3,7,43] := by
  apply (higher_signature_target_iff ![2,3,7,43] (by decide) (by decide +kernel) (by decide)).mpr
  exact ⟨by unfold Pairwise; decide +kernel, by decide +kernel⟩

-- The converse is about the original root subalgebra, with no fixed-ring premise.
example {n a : ℕ} (t : Target (n + 1) a) (hn : 3 ≤ n) :
    rootSubalgebra t.signature t.tau = ⊤ :=
  t.presentation.higher_root_eq_top t.signature t.admissible t.parameter_input t.tau t.root_equation hn

-- The four-coordinate lower bound in the combinatorial step is essential.
example : ∃ S : Fin 3 → Finset (Fin 3),
    (∀ i j : Fin 3, i ≠ j → ∃ k, i ∈ S k ∧ S k ⊆ {i,j}) ∧
    (∀ i k : Fin 3, S k ≠ {i}) := by
  exact ⟨![{0,1}, {1,2}, {0,2}], by decide +kernel, by decide +kernel⟩

end
