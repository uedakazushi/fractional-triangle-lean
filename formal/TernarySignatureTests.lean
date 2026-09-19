import CanonicalRoots.TernaryWeightKey

noncomputable section
open CanonicalRoots

-- These signatures have the same rational root degree at a=1, but different periodic terms.
example : ¬Nonempty (GradedAlgEquiv
    (rootPiece (![2,3,12] : Fin 3 → ℕ) (omegaDegree ![2,3,12]))
    (rootPiece (![2,4,6] : Fin 3 → ℕ) (omegaDegree ![2,4,6]))) := by
  rintro ⟨e⟩
  have h := ternary_root_gradedEquiv_signature_eq ![2,3,12] ![2,4,6]
    ⟨by decide +kernel, by norm_num [Fin.sum_univ_succ]⟩
    ⟨by decide +kernel, by norm_num [Fin.sum_univ_succ]⟩ (by decide : 1 ≤ 1)
    (omegaDegree ![2,3,12]) (omegaDegree ![2,4,6])
    (by simp [IsCanonicalRoot]) (by simp [IsCanonicalRoot]) e
  have hc := congrArg (Multiset.count 3) h
  norm_num [List.ofFn_succ] at hc

-- Repeated entries and their torsion are retained by the signature equivalence.
example : Nonempty (GradedAlgEquiv
    (rootPiece (![3,3,4] : Fin 3 → ℕ) (omegaDegree ![3,3,4]))
    (rootPiece (![4,3,3] : Fin 3 → ℕ) (omegaDegree ![4,3,3]))) := by
  apply root_gradedEquiv_of_signature_multiset_eq _ _ (by decide +kernel) (by decide : 1 ≤ 1)
    _ _ (by simp [IsCanonicalRoot]) (by simp [IsCanonicalRoot])
  decide +kernel

-- The weight criterion quantifies over actual Targets, without assuming a Cox family.
example {a : ℕ} (t s : Target 3 a) :
    Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau) (rootPiece s.signature s.tau)) ↔
      ∃ σ : Equiv.Perm (Fin 3), ∀ i, t.presentation.weights i = s.presentation.weights (σ i) :=
  t.ternary_gradedEquiv_iff_weights s

end
