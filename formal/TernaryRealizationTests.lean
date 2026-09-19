import CanonicalRoots.TernaryRealization

noncomputable section
open CanonicalRoots

-- Every actual target is covered, with no candidate or normal-form hypothesis.
example {a : ℕ} (t : Target 3 a) :
    ∃ e ∈ enumerateTernaryCandidates a,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (candidateRelation e) (candidateNatWeights e))) :=
  t.ternary_enumerated_model

-- Uniform realization includes the root equation, admissibility and isolation in Target.
example {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    (candidateTarget ha he).signature = candidateSignature e ∧
      (candidateTarget ha he).presentation.weights = candidateNatWeights e ∧
      (candidateTarget ha he).presentation.polynomial = candidateRelation e :=
  ⟨candidateTarget_signature ha he,candidateTarget_weights ha he,candidateTarget_polynomial ha he⟩

example : (candidateTarget (by decide) (by decide : ArithmeticTernary 7 ⟨.V,2,3,5⟩)).presentation.weights =
    ![11,9,4] := by
  rw [candidateTarget_weights]
  ext i
  fin_cases i <;> norm_num [candidateNatWeights, candidateWeights, Cox.weights]
