import CanonicalRoots.TernaryClassification

noncomputable section
open CanonicalRoots

-- A cyclic permutation of the loop exponents gives the same actual graded algebra.
example : Nonempty (GradedAlgEquiv
    (presentedPiece (candidateRelation ⟨.V,2,3,5⟩) (candidateNatWeights ⟨.V,2,3,5⟩))
    (presentedPiece (candidateRelation ⟨.V,3,5,2⟩) (candidateNatWeights ⟨.V,3,5,2⟩))) :=
  (candidateKey_eq_iff_gradedEquiv (a := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)).mp (by
    unfold candidateKey
    simp only [List.mergeSort_eq_insertionSort]
    decide +kernel)

-- A different key at the same root index gives a nonisomorphic graded algebra.
example : ¬Nonempty (GradedAlgEquiv
    (presentedPiece (candidateRelation ⟨.V,2,3,5⟩) (candidateNatWeights ⟨.V,2,3,5⟩))
    (presentedPiece (candidateRelation ⟨.I,2,3,13⟩) (candidateNatWeights ⟨.I,2,3,13⟩))) := by
  intro h
  have hh := (candidateKey_eq_iff_gradedEquiv (a := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr h
  have hn : candidateKey ⟨.V,2,3,5⟩ ≠ candidateKey ⟨.I,2,3,13⟩ := by
    unfold candidateKey
    simp only [List.mergeSort_eq_insertionSort]
    decide +kernel
  exact hn hh

example : dedupCandidates [⟨.V,2,3,5⟩,⟨.V,3,5,2⟩,⟨.I,2,3,13⟩,⟨.V,2,3,5⟩] =
    [⟨.V,2,3,5⟩,⟨.I,2,3,13⟩] := by
  unfold dedupCandidates candidateKey
  simp only [List.mergeSort_eq_insertionSort]
  decide +kernel

-- Uniqueness quantifies over output positions and all actual targets.
example {a : ℕ} (t : Target 3 a) :
    ∃! i : Fin (dedupCandidates (enumerateTernaryCandidates a)).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (candidateRelation (ternaryRepresentative a i))
          (candidateNatWeights (ternaryRepresentative a i)))) :=
  t.ternary_representatives_complete_unique
