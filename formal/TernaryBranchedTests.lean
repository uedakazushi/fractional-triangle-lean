import CanonicalRoots.TargetFiveWeights

noncomputable section
open CanonicalRoots

-- B1 weights (3,5,2;35) satisfy the axis degree relations but have only two points.
example : orderMassLinear (coordinateMultiplicity ![3,5,2] 35) = 2 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]

-- B2 weights (4,3,5;23) have three points but violate the defect equation.
example : orderMassLinear (coordinateMultiplicity ![4,3,5] 23) = 3 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]

example : (11 : ℚ) * (23 / (4 * 3 * 5)) - 1 +
    multipleSumLinear 1 (coordinateMultiplicity ![4,3,5] 23) = 4 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, multipleSumLinear_single]

-- This conclusion has no branch, coordinate-data, or classification premise.
example {a : ℕ} (t : Target 3 a) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 5, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧ ∀ i,
        axisWeight t.presentation.weights (σ i)
          (σ (threeAxisPattern ⟨tag.val, by omega⟩ i)) (k i) = t.presentation.relationDegree :=
  t.ternary_five_axis_weights
