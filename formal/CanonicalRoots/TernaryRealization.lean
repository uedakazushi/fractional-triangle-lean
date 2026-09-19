import CanonicalRoots.CoxFermatRealization
import CanonicalRoots.ChainRealization
import CanonicalRoots.LoopRealization
import CanonicalRoots.TargetTernaryCandidate
import CanonicalRoots.TernaryWeightKey

noncomputable section
namespace CanonicalRoots

/-- Every admissible arithmetic candidate has the stated actual isolated graded realization. -/
theorem ternary_candidate_realization {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    ∃ t : Target 3 a, t.signature = candidateSignature e ∧
      (∀ i, (t.presentation.weights i : ℤ) = candidateWeights e i) ∧
      (t.presentation.relationDegree : ℤ) = candidateDegree e ∧
      t.presentation.polynomial = candidateRelation e := by
  obtain ⟨k,α,β,γ⟩ := e
  cases k with
  | I => exact fermat_candidate_realization ha he
  | II => exact monic_candidate_realization ha he (Or.inl rfl)
  | III => exact monic_candidate_realization ha he (Or.inr rfl)
  | IV => exact chain_candidate_realization ha he
  | V => exact loop_candidate_realization ha he

def candidateTarget {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : Target 3 a :=
  Classical.choose (ternary_candidate_realization ha he)

theorem candidateTarget_signature {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : (candidateTarget ha he).signature = candidateSignature e :=
  (Classical.choose_spec (ternary_candidate_realization ha he)).1

theorem candidateTarget_weights {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : (candidateTarget ha he).presentation.weights = candidateNatWeights e := by
  funext i
  apply Int.ofNat_injective
  exact ((Classical.choose_spec (ternary_candidate_realization ha he)).2.1 i).trans
    (candidateNatWeights_cast he i).symm

theorem candidateTarget_degree {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : (candidateTarget ha he).presentation.relationDegree = candidateNatDegree e := by
  apply Int.ofNat_injective
  exact (Classical.choose_spec (ternary_candidate_realization ha he)).2.2.1 |>.trans
    (candidateNatDegree_cast he).symm

theorem candidateTarget_polynomial {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : (candidateTarget ha he).presentation.polynomial = candidateRelation e :=
  (Classical.choose_spec (ternary_candidate_realization ha he)).2.2.2

def candidateTargetGradedEquiv {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    GradedAlgEquiv (presentedPiece (candidateRelation e) (candidateNatWeights e))
      (rootPiece (candidateTarget ha he).signature (candidateTarget ha he).tau) := by
  have hh := (candidateTarget ha he).presentation.graded_equiv
  rw [candidateTarget_polynomial ha he, candidateTarget_weights ha he] at hh
  exact hh

/-- Arbitrary actual ternary root rings admit one of the five concrete Cox models. -/
theorem Target.ternary_candidate_model {a : ℕ} (t : Target 3 a) :
    ∃ e : TernaryCandidate, ArithmeticTernary a e ∧
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (candidateRelation e) (candidateNatWeights e))) := by
  obtain ⟨e,he,σ,_,hw⟩ := t.ternary_arithmetic_candidate
  let s := candidateTarget t.parameter_input he
  have hs : Nonempty (GradedAlgEquiv (rootPiece s.signature s.tau) (rootPiece t.signature t.tau)) := by
    apply (s.ternary_gradedEquiv_iff_weights t).mpr
    refine ⟨σ, fun i => ?_⟩
    rw [show s.presentation.weights = candidateNatWeights e from candidateTarget_weights _ _]
    apply Int.ofNat_injective
    exact (candidateNatWeights_cast he i).trans (hw i)
  obtain ⟨φ⟩ := hs
  exact ⟨e,he,⟨φ.symm.trans (candidateTargetGradedEquiv t.parameter_input he).symm⟩⟩

theorem Target.ternary_enumerated_model {a : ℕ} (t : Target 3 a) :
    ∃ e ∈ enumerateTernaryCandidates a,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (candidateRelation e) (candidateNatWeights e))) := by
  obtain ⟨e,he,hφ⟩ := t.ternary_candidate_model
  exact ⟨e,(enumerateTernaryCandidates_iff a t.parameter_input e).mpr he,hφ⟩

end CanonicalRoots
