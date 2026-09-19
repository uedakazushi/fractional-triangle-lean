import CanonicalRoots.OutputClassification
import Certificates

noncomputable section
open CanonicalRoots

example {n a : ℕ} (t : Target n a) :
    ∃! i : Fin (enumerateCandidateEquations n a).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        ((enumerateCandidateEquations n a).get i).piece) := t.output_complete_unique

example {n a m : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length)
    (q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ((enumerateCandidateEquations n a).get i).Ring)
    (hq : Function.Surjective q) : n ≤ m := output_minimum_generators hn ha i q hq

-- The exact four-variable output is realized by an actual canonical root.
example : ∃ t : Target 4 1,
    t.presentation.polynomial = (higherEquation 1 [2,3,7,43]).polynomial ∧
    t.presentation.weights = (higherEquation 1 [2,3,7,43]).natWeights := by
  obtain ⟨t,_,hw,_,hf⟩ := higherEquation_realization_of_mem (by decide : 3 ≤ 4)
    (by decide : 1 ≤ 1) [2,3,7,43] (by rw [Certificates.higher_4_1_entire_list]; simp)
  exact ⟨t,hf,hw⟩

example (t : Target 4 1) :
    Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
      (higherEquation 1 [2,3,7,43]).piece) := by
  obtain ⟨i,hi,_⟩ := t.output_complete_unique
  have hm := List.get_mem (enumerateCandidateEquations 4 1) i
  simp only [enumerateCandidateEquations, show (4 : ℕ) ≠ 3 from by decide,
    if_false, Certificates.higher_4_1_entire_list, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hm
  change (enumerateCandidateEquations 4 1).get i = higherEquation 1 [2,3,7,43] at hm
  rwa [hm] at hi
