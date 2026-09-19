import CanonicalRoots.CycleWeightPrimitivity

namespace CanonicalRoots.Cox

/-- Cancel a nonzero scale in the already verified Cox homogeneous identities. -/
theorem homogeneous_of_scaled_weights (kind : Kind) (α β γ h κ : ℤ) (w : Fin 3 → ℤ)
    (hκ : κ ≠ 0) (hdeg : degree kind α β γ = κ * h)
    (hw : ∀ i, weights kind α β γ i = κ * w i) :
    ∀ i, ∑ j, exponents kind α β γ i j * w j = h := by
  intro i
  apply mul_left_cancel₀ hκ
  calc
    κ * ∑ j, exponents kind α β γ i j * w j =
        ∑ j, exponents kind α β γ i j * (κ * w j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j, exponents kind α β γ i j * weights kind α β γ j := by simp only [hw]
    _ = degree kind α β γ := homogeneous kind α β γ i
    _ = κ * h := hdeg

end CanonicalRoots.Cox

namespace CanonicalRoots.Target

/-- For an actual Target, a cycle Cox table is already primitive. -/
theorem ternary_cycle_scale_one {a : ℕ} (t : Target 3 a)
    (α β γ κ : ℕ) (hκ : 0 < κ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .V α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .V α β γ i = (κ : ℤ) * t.presentation.weights (σ i)) : κ = 1 := by
  let A := t.presentation.weights (σ 0)
  let B := t.presentation.weights (σ 1)
  let C := t.presentation.weights (σ 2)
  let h := t.presentation.relationDegree
  have hhom := Cox.homogeneous_of_scaled_weights .V α β γ h κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) (by exact_mod_cast ne_of_gt hκ) hdeg hw
  have h0 : α * A + B = h := by
    have he := hhom 0
    simp [Cox.exponents, Fin.sum_univ_three] at he
    exact_mod_cast he
  have h1 : β * B + C = h := by
    have he := hhom 1
    simp [Cox.exponents, Fin.sum_univ_three] at he
    exact_mod_cast he
  have h2 : γ * C + A = h := by
    have he := hhom 2
    simp [Cox.exponents, Fin.sum_univ_three] at he
    have he' : (γ : ℤ) * C + A = h := by dsimp [A, C, h]; linarith
    exact_mod_cast he'
  have hk : (κ : ℚ) * A = (γ : ℚ) * ((β : ℚ) - 1) + 1 := by
    have he : (κ : ℤ) * A = (γ : ℤ) * ((β : ℤ) - 1) + 1 := by
      simpa [Cox.weights, A] using (hw 0).symm
    exact_mod_cast he
  obtain ⟨hp, hd, hm, hz⟩ := t.ternary_permuted_coordinate_constraints σ
  exact cycle_weight_scale_one A B C h a α β γ κ
    (t.presentation.weights_pos _) (t.presentation.weights_pos _) (t.presentation.weights_pos _)
    h0 h1 h2 hp
    (t.ternary_pair_weight_gcd_dvd (σ 0) (σ 1) (σ.injective.ne (by decide)))
    (t.ternary_pair_weight_gcd_dvd (σ 0) (σ 2) (σ.injective.ne (by decide)))
    (t.ternary_pair_weight_gcd_dvd (σ 1) (σ 2) (σ.injective.ne (by decide))) hd hk hm hz

end CanonicalRoots.Target
