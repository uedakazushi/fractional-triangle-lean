import CanonicalRoots.CoxWeightNormalization

open CanonicalRoots

-- The nonprimitive Fermat presentation must retain scale two.
example : Cox.degree .I 2 3 8 = (2 : ℤ) * 24 ∧
    ∀ i, Cox.weights .I 2 3 8 i = (2 : ℤ) * (![12,8,3] : Fin 3 → ℤ) i := by
  constructor
  · norm_num [Cox.degree]
  · intro i; fin_cases i <;> norm_num [Cox.weights]

example : Finset.univ.gcd (fun i : Fin 3 => (Cox.weights .I 2 3 8 i).toNat) = 2 := by
  decide +kernel

-- The generic normalization theorem obtains the integer factor from primitive weights.
example : ∃ κ : ℕ, 0 < κ ∧ (48 : ℕ) = κ * 24 ∧
    (∀ i, (![24,16,6] : Fin 3 → ℕ) i = κ * (![12,8,3] : Fin 3 → ℕ) i) ∧
    Finset.univ.gcd (![24,16,6] : Fin 3 → ℕ) = κ := by
  apply primitive_weights_integer_scale ![12,8,3] ![24,16,6] 24 48 (by decide) (by decide)
  · decide +kernel
  · intro i; fin_cases i <;> norm_num

example {a : ℕ} (t : Target 3 a) :
    ∃ kind : Cox.Kind, ∃ α β γ κ : ℕ, ∃ σ : Equiv.Perm (Fin 3),
      2 ≤ α ∧ 2 ≤ β ∧ 2 ≤ γ ∧ 0 < κ ∧
      Cox.degree kind α β γ = (κ : ℤ) * t.presentation.relationDegree ∧
      (∀ i, Cox.weights kind α β γ i = (κ : ℤ) * t.presentation.weights (σ i)) ∧
      Finset.univ.gcd (fun i => (Cox.weights kind α β γ i).toNat) = κ :=
  t.ternary_scaled_cox_weights
