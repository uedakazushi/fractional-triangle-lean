import CanonicalRoots.TargetPrimitiveReduction

noncomputable section
open CanonicalRoots

-- III (3,4,5), primitive: all three recovered orders survive.
example : orderMassLinear (coordinateMultiplicity ![15,10,11] 55) = 3 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]
example : multipleSumLinear 1 (coordinateMultiplicity ![15,10,11] 55) = 11/30 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, multipleSumLinear_single]

-- IV (3,3,5), primitive; its two-vertex profile is (11,12,3).
example : orderMassLinear (coordinateMultiplicity ![11,12,9] 45) = 3 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]
example : multipleSumLinear 1 (coordinateMultiplicity ![11,12,9] 45) = 67/132 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, multipleSumLinear_single]

-- Nonprimitive IV (3,4,5), scaled by 4: violates the actual three-point mass.
example : orderMassLinear (coordinateMultiplicity ![4,3,3] 15) = 6 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]

-- No extra classification or saturated-support hypothesis is needed on a Target.
example {a : ℕ} (t : Target 3 a) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 5, ∃ k : Fin 3 → ℕ, ∃ κ : ℕ,
      (∀ i, 2 ≤ k i) ∧ 0 < κ ∧
      Cox.degree (axisKind tag) (k 0) (k 1) (k 2) = (κ : ℤ) * t.presentation.relationDegree ∧
      (∀ i, Cox.weights (axisKind tag) (k 0) (k 1) (k 2) i = (κ : ℤ) * t.presentation.weights (σ i)) ∧
      Finset.univ.gcd (fun i => (Cox.weights (axisKind tag) (k 0) (k 1) (k 2) i).toNat) = κ ∧
      (∀ i, t.presentation.weights (σ i) ∣ t.presentation.relationDegree ↔
        i = threeAxisPattern ⟨tag.val, by omega⟩ i) ∧
      (tag.val < 2 ∨ κ = 1) := t.ternary_saturated_scaled_cox_weights
