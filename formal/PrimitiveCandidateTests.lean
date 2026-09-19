import CanonicalRoots.TargetTernaryCandidate

noncomputable section
open CanonicalRoots

-- Quadratic pure exception: I(2,4,5)/2 -> II(2,2,5), swapping two weights.
example : orderMassLinear (coordinateMultiplicity ![10,5,4] 20) = 3 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]
example : ArithmeticTernary 1 ⟨.II,2,2,5⟩ := by decide
example : (⟨.II,2,2,5⟩ : TernaryCandidate) ∈ enumerateTernaryCandidates 1 := by
  exact (enumerateTernaryCandidates_iff 1 (by decide) _).mpr (by decide)

-- Cubic pure exception: all three signature entries coincide.
example : orderMassLinear (coordinateMultiplicity ![4,4,3] 12) = 3 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]
example : multipleSumLinear 1 (coordinateMultiplicity ![4,4,3] 12) = 3/4 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, multipleSumLinear_single]
example : ArithmeticTernary 1 ⟨.III,2,2,4⟩ := by decide

-- Actual Target is the only hypothesis, independently of any finite search.
example {a : ℕ} (t : Target 3 a) :
    ∃ e : TernaryCandidate, ArithmeticTernary a e ∧
      ∃ σ : Equiv.Perm (Fin 3), candidateDegree e = t.presentation.relationDegree ∧
        ∀ i, candidateWeights e i = t.presentation.weights (σ i) := t.ternary_arithmetic_candidate
example {a : ℕ} (t : Target 3 a) :
    ∃ e ∈ enumerateTernaryCandidates a,
      ∃ σ : Equiv.Perm (Fin 3), candidateDegree e = t.presentation.relationDegree ∧
        ∀ i, candidateWeights e i = t.presentation.weights (σ i) := t.ternary_enumerated_weight_candidate
