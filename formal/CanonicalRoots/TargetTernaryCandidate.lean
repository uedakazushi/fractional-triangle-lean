import CanonicalRoots.TargetPrimitiveWeights
import CanonicalRoots.Candidates

noncomputable section
namespace CanonicalRoots.Target

/-- Necessary classification into the unbounded, independent arithmetic predicate.
Candidate membership is derived afterwards, not assumed in the Target. -/
theorem ternary_arithmetic_candidate {a : ℕ} (t : Target 3 a) :
    ∃ e : TernaryCandidate, ArithmeticTernary a e ∧
      ∃ σ : Equiv.Perm (Fin 3), candidateDegree e = t.presentation.relationDegree ∧
        ∀ i, candidateWeights e i = t.presentation.weights (σ i) := by
  obtain ⟨kind, α, β, γ, σ, hα, hβ, hγ, hd, hw⟩ := t.ternary_primitive_cox_weights
  let e : TernaryCandidate := ⟨kind, α, β, γ⟩
  refine ⟨e, ⟨hα, hβ, hγ, ?_, ?_⟩, σ, hd, hw⟩
  · change Int.gcd (Cox.weights kind α β γ 0)
      (Int.gcd (Cox.weights kind α β γ 1) (Cox.weights kind α β γ 2)) = 1
    rw [hw 0, hw 1, hw 2]
    simp only [Int.gcd_natCast_natCast, ← Nat.gcd_assoc]
    exact primitive_ternary_gcd_perm _ t.weights_gcd_eq_one σ
  · change Cox.defect kind α β γ = a
    simpa using t.ternary_cox_defect kind α β γ 1 σ (by simpa using hd) (by simpa using hw)

/-- Every actual ternary Target has a weight-matching entry in the proved finite
arithmetic enumeration. Realization of all entries is a separate obligation. -/
theorem ternary_enumerated_weight_candidate {a : ℕ} (t : Target 3 a) :
    ∃ e ∈ enumerateTernaryCandidates a,
      ∃ σ : Equiv.Perm (Fin 3), candidateDegree e = t.presentation.relationDegree ∧
        ∀ i, candidateWeights e i = t.presentation.weights (σ i) := by
  obtain ⟨e, he, σ, hd, hw⟩ := t.ternary_arithmetic_candidate
  exact ⟨e, (enumerateTernaryCandidates_iff a t.parameter_input e).mpr he, σ, hd, hw⟩

end CanonicalRoots.Target
