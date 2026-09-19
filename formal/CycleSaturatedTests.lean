import CanonicalRoots.TargetCyclePrimitive
import CanonicalRoots.NumericPureSaturation

noncomputable section
open CanonicalRoots

-- Positive defect alone does not make the cycle (2,2,5), raw gcd=3, a Target.
example : orderMassLinear (coordinateMultiplicity ![2,3,1] 7) = 2 := by
  rw [coordinateMultiplicity_three]
  norm_num [weightedOrderAtom, map_add, orderMassLinear_single]

example : (7 : ℚ) * (31 / (11 * 9 * 4)) - 1 + (1/11 + 1/9 + 1/4) = 0 := by
  norm_num

example {a : ℕ} (t : Target 3 a) (α β γ κ : ℕ) (hκ : 0 < κ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .V α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .V α β γ i = (κ : ℤ) * t.presentation.weights (σ i)) : κ = 1 :=
  t.ternary_cycle_scale_one α β γ κ hκ σ hdeg hw

-- All available pure powers are chosen, an iff rather than a one-way loop property.
example {a : ℕ} (t : Target 3 a) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 5, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧
      (∀ i, axisWeight t.presentation.weights (σ i)
        (σ (threeAxisPattern ⟨tag.val, by omega⟩ i)) (k i) = t.presentation.relationDegree) ∧
      ∀ i, t.presentation.weights (σ i) ∣ t.presentation.relationDegree ↔
        i = threeAxisPattern ⟨tag.val, by omega⟩ i :=
  t.ternary_five_saturated_weights
