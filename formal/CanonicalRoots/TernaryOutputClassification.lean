import CanonicalRoots.TernaryClassification
import CanonicalRoots.TernaryEquationSemantics

noncomputable section
namespace CanonicalRoots

/-- The unpermuted Cox model and its exact serialized presentation are graded-isomorphic. -/
def ternaryEquationModelEquiv (a : ℕ) (e : TernaryCandidate) :
    GradedAlgEquiv (presentedPiece (candidateRelation e) (candidateNatWeights e))
      (ternaryEquation a e).piece := by
  change GradedAlgEquiv _ (presentedPiece (ternaryEquation a e).polynomial (ternaryEquation a e).natWeights)
  rw [ternaryEquation_polynomial, ternaryEquation_natWeights]
  exact presentedGradedRename _ _ (displayVariablePermutation (candidateWeights e)).symm

def ternaryOutputIndex (a : ℕ) : Fin (enumerateCandidateEquations 3 a).length ≃
    Fin (dedupCandidates (enumerateTernaryCandidates a)).length :=
  finCongr (by simp [enumerateCandidateEquations])

theorem ternary_output_get (a : ℕ) (i : Fin (enumerateCandidateEquations 3 a).length) :
    (enumerateCandidateEquations 3 a).get i =
      ternaryEquation a (ternaryRepresentative a (ternaryOutputIndex a i)) := by
  have hi : i.val < (dedupCandidates (enumerateTernaryCandidates a)).length := by
    simpa [enumerateCandidateEquations] using i.isLt
  have hj : i.val < ((dedupCandidates (enumerateTernaryCandidates a)).map (ternaryEquation a)).length := by
    simpa using hi
  change ((dedupCandidates (enumerateTernaryCandidates a)).map (ternaryEquation a))[i.val]'hj =
    ternaryEquation a ((dedupCandidates (enumerateTernaryCandidates a))[i.val]'hi)
  simp only [List.getElem_map]

theorem ternary_output_sound {a : ℕ} (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations 3 a).length) :
    ∃ t : Target ((enumerateCandidateEquations 3 a).get i).n a,
      t.presentation.polynomial = ((enumerateCandidateEquations 3 a).get i).polynomial ∧
      t.presentation.weights = ((enumerateCandidateEquations 3 a).get i).natWeights ∧
      (t.presentation.relationDegree : ℤ) = ((enumerateCandidateEquations 3 a).get i).relationDegree := by
  rw [ternary_output_get]
  obtain ⟨t,_,hw,hd,hf⟩ := ternaryEquation_realization ha
    (ternaryRepresentative_arithmetic ha (ternaryOutputIndex a i))
  exact ⟨t,hf,hw,hd⟩

theorem ternary_output_pairwise_nonisomorphic {a : ℕ} (ha : 1 ≤ a)
    (i j : Fin (enumerateCandidateEquations 3 a).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv ((enumerateCandidateEquations 3 a).get i).piece
      ((enumerateCandidateEquations 3 a).get j).piece) := by
  rw [ternary_output_get, ternary_output_get]
  rintro ⟨φ⟩
  apply ternary_representatives_pairwise_nonisomorphic ha (ternaryOutputIndex a i) (ternaryOutputIndex a j)
    ((ternaryOutputIndex a).injective.ne hij)
  exact ⟨(ternaryEquationModelEquiv a _).trans (φ.trans (ternaryEquationModelEquiv a _).symm)⟩

theorem Target.ternary_output_complete_unique {a : ℕ} (t : Target 3 a) :
    ∃! i : Fin (enumerateCandidateEquations 3 a).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        ((enumerateCandidateEquations 3 a).get i).piece) := by
  obtain ⟨j,⟨φ⟩,_⟩ := t.ternary_representatives_complete_unique
  let i := (ternaryOutputIndex a).symm j
  have hi : Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
      ((enumerateCandidateEquations 3 a).get i).piece) := by
    rw [ternary_output_get, show ternaryOutputIndex a i = j from (ternaryOutputIndex a).apply_symm_apply j]
    exact ⟨φ.trans (ternaryEquationModelEquiv a _)⟩
  refine ⟨i,hi,?_⟩
  rintro k ⟨ψ⟩
  by_contra hki
  obtain ⟨χ⟩ := hi
  exact ternary_output_pairwise_nonisomorphic t.parameter_input k i hki ⟨ψ.symm.trans χ⟩

end CanonicalRoots
