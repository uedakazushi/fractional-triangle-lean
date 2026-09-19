import CanonicalRoots.HigherClassification
import CanonicalRoots.HigherEquationRealization

noncomputable section
namespace CanonicalRoots

def higherOutputIndex (n a : ℕ) (hn : n ≠ 3) :
    Fin (enumerateCandidateEquations n a).length ≃
      Fin (enumerateHigherCandidates n a).length :=
  finCongr (by simp [enumerateCandidateEquations, hn])

theorem higher_output_get (n a : ℕ) (hn : n ≠ 3)
    (i : Fin (enumerateCandidateEquations n a).length) :
    (enumerateCandidateEquations n a).get i =
      higherEquation a ((enumerateHigherCandidates n a).get (higherOutputIndex n a hn i)) := by
  have hi : i.val < (enumerateHigherCandidates n a).length := by
    simpa [enumerateCandidateEquations, hn] using i.isLt
  have hj : i.val < ((enumerateHigherCandidates n a).map (higherEquation a)).length := by
    simpa using hi
  rw [List.get_of_eq (show enumerateCandidateEquations n a =
    (enumerateHigherCandidates n a).map (higherEquation a) from by
      simp [enumerateCandidateEquations, hn])]
  change ((enumerateHigherCandidates n a).map (higherEquation a))[i.val]'hj =
    higherEquation a ((enumerateHigherCandidates n a)[i.val]'hi)
  simp only [List.getElem_map]

def higherOutputModelEquiv (n a : ℕ) (hn : n ≠ 3) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    GradedAlgEquiv
      (presentedPiece (fermat (higherCandidateSignature n a ha (higherOutputIndex n a hn i)))
        (productWeights (higherCandidateSignature n a ha (higherOutputIndex n a hn i))))
      ((enumerateCandidateEquations n a).get i).piece := by
  rw [higher_output_get n a hn, ← ofFn_higherCandidateSignature n a ha]
  apply higherEquationOfFnModelEquiv
  intro j
  have hm := List.get_mem (enumerateHigherCandidates n a) (higherOutputIndex n a hn i)
  have hA := (enumerateHigherCandidates_iff n a ha _).mp hm
  exact lt_of_lt_of_le (by decide) (hA.2.1 _ (List.get_mem _ _))

theorem higher_output_sound {n a : ℕ} (hn : 4 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateCandidateEquations n a).length) :
    ∃ t : Target ((enumerateCandidateEquations n a).get i).n a,
      t.presentation.polynomial = ((enumerateCandidateEquations n a).get i).polynomial ∧
      t.presentation.weights = ((enumerateCandidateEquations n a).get i).natWeights ∧
      (t.presentation.relationDegree : ℤ) = ((enumerateCandidateEquations n a).get i).relationDegree := by
  rw [higher_output_get n a (by omega)]
  obtain ⟨t,_,hw,hd,hf⟩ := higherEquation_realization_of_mem (by omega : 3 ≤ n) ha _
    (List.get_mem _ (higherOutputIndex n a (by omega) i))
  exact ⟨t,hf,hw,hd⟩

theorem higher_output_pairwise_nonisomorphic {n a : ℕ} (hn : n ≠ 3) (ha : 1 ≤ a)
    (i j : Fin (enumerateCandidateEquations n a).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv ((enumerateCandidateEquations n a).get i).piece
      ((enumerateCandidateEquations n a).get j).piece) := by
  rintro ⟨φ⟩
  apply higher_candidates_pairwise_nonisomorphic ha (higherOutputIndex n a hn i)
    (higherOutputIndex n a hn j) ((higherOutputIndex n a hn).injective.ne hij)
  exact ⟨(higherOutputModelEquiv n a hn ha i).trans
    (φ.trans (higherOutputModelEquiv n a hn ha j).symm)⟩

theorem Target.higher_output_complete_unique {n a : ℕ} (t : Target (n + 1) a) (hn : 3 ≤ n) :
    ∃! i : Fin (enumerateCandidateEquations (n + 1) a).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        ((enumerateCandidateEquations (n + 1) a).get i).piece) := by
  have hn3 : n + 1 ≠ 3 := by omega
  obtain ⟨j,⟨φ⟩,_⟩ := t.higher_candidates_complete_unique hn
  let i := (higherOutputIndex (n + 1) a hn3).symm j
  have hi : Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
      ((enumerateCandidateEquations (n + 1) a).get i).piece) := by
    have ψ := higherOutputModelEquiv (n + 1) a hn3 t.parameter_input i
    rw [show higherOutputIndex (n + 1) a hn3 i = j from
      (higherOutputIndex (n + 1) a hn3).apply_symm_apply j] at ψ
    exact ⟨φ.trans ψ⟩
  refine ⟨i,hi,?_⟩
  rintro k ⟨ψ⟩
  by_contra hki
  obtain ⟨χ⟩ := hi
  exact higher_output_pairwise_nonisomorphic hn3 t.parameter_input k i hki ⟨ψ.symm.trans χ⟩

end CanonicalRoots
