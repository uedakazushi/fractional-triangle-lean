import CanonicalRoots.TernaryOutputClassification
import Certificates

noncomputable section
open CanonicalRoots

-- The actual equation list, including variable ordering, classifies each actual ternary target.
example {a : ℕ} (t : Target 3 a) :
    ∃! i : Fin (enumerateCandidateEquations 3 a).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        ((enumerateCandidateEquations 3 a).get i).piece) :=
  t.ternary_output_complete_unique

example (i j : Fin (enumerateCandidateEquations 3 1).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv ((enumerateCandidateEquations 3 1).get i).piece
      ((enumerateCandidateEquations 3 1).get j).piece) :=
  ternary_output_pairwise_nonisomorphic (by decide) i j hij

-- The existing complete-list certificate now implies absence of every actual a=6 target.
example : IsEmpty (Target 3 6) := by
  refine ⟨fun t => ?_⟩
  obtain ⟨i,_,_⟩ := t.ternary_output_complete_unique
  have hi := i.isLt
  simp [enumerateCandidateEquations, Certificates.ternary_6_entire_list, Certificates.explicitTernary6] at hi
