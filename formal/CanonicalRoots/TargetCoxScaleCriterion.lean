import CanonicalRoots.CoxScaledMultiplicity
import CanonicalRoots.TargetCyclePrimitive

namespace CanonicalRoots.Cox

theorem defect_of_scaled_weights (kind : Kind) (α β γ h a κ : ℤ) (w : Fin 3 → ℤ)
    (hdef : h = a + ∑ i, w i) (hdeg : degree kind α β γ = κ * h)
    (hw : ∀ i, weights kind α β γ i = κ * w i) : defect kind α β γ = κ * a := by
  simp only [defect, hdeg, hw, ← Finset.mul_sum]
  rw [hdef]
  ring

end CanonicalRoots.Cox

noncomputable section
namespace CanonicalRoots.Target

/-- A reusable primitive criterion: a scaled Cox signature that reproduces the
actual reciprocal profile forces its common factor to be one. -/
theorem ternary_scale_one_of_signature_scale {a : ℕ} (t : Target 3 a)
    (kind : Cox.Kind) (α β γ κ : ℕ) (hκ : 0 < κ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree kind α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights kind α β γ i = (κ : ℤ) * t.presentation.weights (σ i))
    (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hsig : ∀ i, Cox.signature kind α β γ i = (κ : ℤ) * p i)
    (hprofile : multipleSumLinear 1 (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) =
      ∑ i, (1 : ℚ) / p i) : κ = 1 := by
  have hsum : ∑ i, (t.presentation.weights (σ i) : ℤ) = ∑ i, (t.presentation.weights i : ℤ) :=
    Equiv.sum_comp σ (fun i => (t.presentation.weights i : ℤ))
  have hdef : (t.presentation.relationDegree : ℤ) = (a : ℤ) + ∑ i, (t.presentation.weights (σ i) : ℤ) := by
    rw [hsum]
    exact_mod_cast t.relationDegree_eq_add_sum_weights
  have ha := Cox.defect_of_scaled_weights kind α β γ t.presentation.relationDegree a κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) hdef hdeg hw
  have heq := Cox.scaled_signature_defect kind α β γ
    (fun i => (t.presentation.weights (σ i) : ℚ)) (fun i => (p i : ℚ)) a t.presentation.relationDegree κ
    (fun i => by exact_mod_cast ne_of_gt (t.presentation.weights_pos (σ i)))
    (fun i => by exact_mod_cast ne_of_gt (hp i))
    (by exact_mod_cast ne_of_gt hκ)
    (fun i => by exact_mod_cast hw i) (fun i => by exact_mod_cast hsig i)
    (by exact_mod_cast hdeg) (by exact_mod_cast ha)
  have hprod : ∏ i, (t.presentation.weights (σ i) : ℚ) = ∏ i, (t.presentation.weights i : ℚ) :=
    Equiv.prod_comp σ (fun i => (t.presentation.weights i : ℚ))
  rw [hprod, ← hprofile, t.coordinateMultiplicity_defect] at heq
  have : (κ : ℚ) = 1 := by linarith
  exact_mod_cast this

end CanonicalRoots.Target
