import CanonicalRoots.TargetCoxScaleCriterion

namespace CanonicalRoots.Target

/-- The defect in a raw Cox table equals its scale times the actual root parameter. -/
theorem ternary_cox_defect {a : ℕ} (t : Target 3 a)
    (kind : Cox.Kind) (α β γ κ : ℕ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree kind α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights kind α β γ i = (κ : ℤ) * t.presentation.weights (σ i)) :
    Cox.defect kind α β γ = (κ : ℤ) * a := by
  have hsum : ∑ i, (t.presentation.weights (σ i) : ℤ) = ∑ i, (t.presentation.weights i : ℤ) :=
    Equiv.sum_comp σ (fun i => (t.presentation.weights i : ℤ))
  apply Cox.defect_of_scaled_weights kind α β γ t.presentation.relationDegree a κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) _ hdeg hw
  rw [hsum]
  exact_mod_cast t.relationDegree_eq_add_sum_weights

end CanonicalRoots.Target
