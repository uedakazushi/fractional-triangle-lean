import CanonicalRoots.TernaryRealization

noncomputable section
namespace CanonicalRoots

theorem candidateKey_sorted_weights {e f : TernaryCandidate} (h : candidateKey e = candidateKey f) :
    ([candidateWeights e 0,candidateWeights e 1,candidateWeights e 2].mergeSort (· ≤ ·)) =
      ([candidateWeights f 0,candidateWeights f 1,candidateWeights f 2].mergeSort (· ≤ ·)) := by
  have hh := congrArg (List.take 3) h
  simpa [candidateKey, List.take_append] using hh

theorem candidateKey_weights_permutation {e f : TernaryCandidate}
    (h : candidateKey e = candidateKey f) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i, candidateNatWeights e i = candidateNatWeights f (σ i) := by
  have hs := candidateKey_sorted_weights h
  have hp : List.Perm [candidateWeights e 0,candidateWeights e 1,candidateWeights e 2]
      [candidateWeights f 0,candidateWeights f 1,candidateWeights f 2] := by
    apply (List.mergeSort_perm _ (fun x y : ℤ => decide (x ≤ y))).symm.trans
    rw [hs]
    exact List.mergeSort_perm _ _
  have hn : (List.ofFn (candidateNatWeights e) : Multiset ℕ) = List.ofFn (candidateNatWeights f) := by
    apply Multiset.coe_eq_coe.mpr
    simpa [candidateNatWeights, List.ofFn_succ] using hp.map Int.toNat
  obtain ⟨σ,hσ⟩ := signature_permutation_of_multiset_eq _ _ hn
  exact ⟨σ,fun i => congrFun hσ i⟩

theorem candidateKey_eq_of_weights_permutation {a : ℕ} {e f : TernaryCandidate}
    (he : ArithmeticTernary a e) (hf : ArithmeticTernary a f)
    (σ : Equiv.Perm (Fin 3)) (hw : ∀ i, candidateNatWeights e i = candidateNatWeights f (σ i)) :
    candidateKey e = candidateKey f := by
  have hwi : candidateWeights e = candidateWeights f ∘ σ := by
    funext i
    change candidateWeights e i = candidateWeights f (σ i)
    rw [← candidateNatWeights_cast he, ← candidateNatWeights_cast hf, hw]
  have hp : List.Perm [candidateWeights e 0,candidateWeights e 1,candidateWeights e 2]
      [candidateWeights f 0,candidateWeights f 1,candidateWeights f 2] := by
    have hh := σ.ofFn_comp_perm (candidateWeights f)
    rw [← hwi] at hh
    simpa [List.ofFn_succ, Fin.reduceFinMk] using hh
  have hs := ((List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm)).eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤ ·) _) (List.pairwise_mergeSort' (· ≤ ·) _)
  have hd : candidateDegree e = candidateDegree f := by
    rw [← candidateNatDegree_cast he, ← candidateNatDegree_cast hf,
      candidateNatDegree_eq_add_sum_weights he, candidateNatDegree_eq_add_sum_weights hf]
    congr 2
    simp_rw [hw]
    exact Equiv.sum_comp σ _
  exact congrArg₂ (· ++ ·) hs (congrArg (fun z => [z]) hd)

/-- The executable ternary key is a complete invariant of the actual graded quotient models. -/
theorem candidateKey_eq_iff_gradedEquiv {a : ℕ} (ha : 1 ≤ a) {e f : TernaryCandidate}
    (he : ArithmeticTernary a e) (hf : ArithmeticTernary a f) :
    candidateKey e = candidateKey f ↔
      Nonempty (GradedAlgEquiv (presentedPiece (candidateRelation e) (candidateNatWeights e))
        (presentedPiece (candidateRelation f) (candidateNatWeights f))) := by
  constructor
  · intro h
    obtain ⟨σ,hw⟩ := candidateKey_weights_permutation h
    have ht : Nonempty (GradedAlgEquiv
        (rootPiece (candidateTarget ha he).signature (candidateTarget ha he).tau)
        (rootPiece (candidateTarget ha hf).signature (candidateTarget ha hf).tau)) := by
      apply ((candidateTarget ha he).ternary_gradedEquiv_iff_weights (candidateTarget ha hf)).mpr
      exact ⟨σ, by simpa only [candidateTarget_weights] using hw⟩
    obtain ⟨φ⟩ := ht
    exact ⟨(candidateTargetGradedEquiv ha he).trans (φ.trans (candidateTargetGradedEquiv ha hf).symm)⟩
  · rintro ⟨φ⟩
    obtain ⟨σ,hw⟩ := gradedEquiv_weights_permutation _ _
      (candidateRelation_no_constant_or_linear ha he) (candidateRelation_no_constant_or_linear ha hf)
      _ _ (candidateNatWeights_pos he) φ
    exact candidateKey_eq_of_weights_permutation he hf σ hw

end CanonicalRoots
