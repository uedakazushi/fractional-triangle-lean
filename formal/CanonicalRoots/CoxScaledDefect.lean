import CanonicalRoots.TargetCoxScaleCriterion

namespace CanonicalRoots.Cox

/-- The Cox defect identity with normalized weights but unnormalized signature. -/
theorem scaled_weight_defect (kind : Kind) (α β γ : ℤ)
    (w : Fin 3 → ℚ) (a h κ : ℚ) (hw0 : ∀ i, w i ≠ 0)
    (hs0 : ∀ i, signature kind α β γ i ≠ 0) (hκ : κ ≠ 0)
    (hw : ∀ i, (weights kind α β γ i : ℚ) = κ * w i)
    (hd : (degree kind α β γ : ℚ) = κ * h)
    (ha : (defect kind α β γ : ℚ) = κ * a) :
    a * (h / ∏ i, w i) - 1 + ∑ i, κ / (signature kind α β γ i : ℚ) = κ - 1 := by
  have hs (i : Fin 3) : (signature kind α β γ i : ℚ) ≠ 0 := by exact_mod_cast hs0 i
  have he := scaled_signature_defect kind α β γ w
    (fun i => (signature kind α β γ i : ℚ) / κ) a h κ hw0
    (fun i => div_ne_zero (hs i) hκ) hκ hw
    (fun i => by field_simp) hd ha
  simpa only [one_div_div] using he

end CanonicalRoots.Cox

noncomputable section
namespace CanonicalRoots.Target

/-- The actual coordinate profile satisfies the Cox defect identity with scale. -/
theorem ternary_scaled_defect_profile {a : ℕ} (t : Target 3 a)
    (kind : Cox.Kind) (α β γ κ : ℕ) (hκ : 0 < κ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree kind α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights kind α β γ i = (κ : ℤ) * t.presentation.weights (σ i))
    (hs0 : ∀ i, Cox.signature kind α β γ i ≠ 0) :
    (κ : ℚ) - ∑ i, (κ : ℚ) / (Cox.signature kind α β γ i : ℚ) +
      multipleSumLinear 1 (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) = 1 := by
  have hsum : ∑ i, (t.presentation.weights (σ i) : ℤ) = ∑ i, (t.presentation.weights i : ℤ) :=
    Equiv.sum_comp σ (fun i => (t.presentation.weights i : ℤ))
  have hdef : (t.presentation.relationDegree : ℤ) = (a : ℤ) + ∑ i, (t.presentation.weights (σ i) : ℤ) := by
    rw [hsum]
    exact_mod_cast t.relationDegree_eq_add_sum_weights
  have ha := Cox.defect_of_scaled_weights kind α β γ t.presentation.relationDegree a κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) hdef hdeg hw
  have he := Cox.scaled_weight_defect kind α β γ
    (fun i => (t.presentation.weights (σ i) : ℚ)) a t.presentation.relationDegree κ
    (fun i => by exact_mod_cast ne_of_gt (t.presentation.weights_pos (σ i))) hs0
    (by exact_mod_cast ne_of_gt hκ) (fun i => by exact_mod_cast hw i)
    (by exact_mod_cast hdeg) (by exact_mod_cast ha)
  have hprod : ∏ i, (t.presentation.weights (σ i) : ℚ) = ∏ i, (t.presentation.weights i : ℚ) :=
    Equiv.prod_comp σ (fun i => (t.presentation.weights i : ℚ))
  rw [hprod] at he
  have hd := t.coordinateMultiplicity_defect
  linarith

end CanonicalRoots.Target
