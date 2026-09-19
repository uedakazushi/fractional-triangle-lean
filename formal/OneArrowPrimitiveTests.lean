import CanonicalRoots.TargetOneArrowPrimitive
import CanonicalRoots.ThreePairOrientation

noncomputable section
open CanonicalRoots

-- II(2,5,3)/2 = III(2,3,3), including the two repeated recovered orders.
example : orderMassLinear (coordinateMultiplicity ![6,3,5] 15) = 3 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]
example : Cox.weights .III 2 3 3 = ![6,3,5] := by decide
example : multipleSumLinear 1 (coordinateMultiplicity ![6,3,5] 15) = 5/6 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, multipleSumLinear_single]

-- II(3,8,2)/2 = IV(3,4,2).
example : orderMassLinear (coordinateMultiplicity ![7,3,12] 24) = 3 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]
example : Cox.weights .IV 3 4 2 = ![7,3,12] := by decide
example : multipleSumLinear 1 (coordinateMultiplicity ![7,3,12] 24) = 17/21 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, multipleSumLinear_single]

example {a : ℕ} (t : Target 3 a) (α β γ κ : ℕ)
    (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (hκ : 0 < κ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .II α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .II α β γ i = (κ : ℤ) * t.presentation.weights (σ i))
    (hnA : ¬ t.presentation.weights (σ 0) ∣ t.presentation.relationDegree) :
    ∃ kind : Cox.Kind, ∃ α' β' γ' : ℕ,
      2 ≤ α' ∧ 2 ≤ β' ∧ 2 ≤ γ' ∧
      Cox.degree kind α' β' γ' = t.presentation.relationDegree ∧
      ∀ i, Cox.weights kind α' β' γ' i = t.presentation.weights (σ i) :=
  t.ternary_oneArrow_primitive_weights α β γ κ hα hβ hγ hκ σ hdeg hw hnA
