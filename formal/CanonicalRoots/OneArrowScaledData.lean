import CanonicalRoots.OneArrowScaleCases

noncomputable section
namespace CanonicalRoots

/-- The two pair orders are controlled by exponent gcds in the raw type-II table. -/
theorem oneArrow_scaled_pair_orders (A B C α γ e κ : ℕ)
    (h0 : γ * e = κ * A) (h1 : α * γ = κ * B) (h2 : α * (e + 1) = κ * C) :
    κ * Nat.gcd A B = γ * Nat.gcd e α ∧
      κ * Nat.gcd B C = α * Nat.gcd γ (e + 1) := by
  constructor
  · rw [← Nat.gcd_mul_left, ← h0, ← h1, Nat.mul_comm α γ, Nat.gcd_mul_left]
  · rw [← Nat.gcd_mul_left, ← h1, ← h2, Nat.gcd_mul_left]

/-- The two pair coefficients in type II are the corresponding scaled reciprocals. -/
theorem oneArrow_scaled_coordinateMultiplicity (A B C α γ e h κ : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hα : 0 < α) (hγ : 0 < γ)
    (hh : h = (e + 1) * B) (hnA : ¬ A ∣ h) (hdC : C ∣ h) (hAC : Nat.Coprime A C)
    (h0 : γ * e = κ * A) (h2 : α * (e + 1) = κ * C) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom A (A : ℚ)⁻¹ +
      weightedOrderAtom (Nat.gcd A B) ((κ : ℚ) / γ) +
      weightedOrderAtom (Nat.gcd B C) ((κ : ℚ) / α) := by
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  have hα0 : (α : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hα
  have hγ0 : (γ : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hγ
  have hc : (e : ℚ) / A = (κ : ℚ) / γ := by
    apply (div_eq_div_iff hA0 hγ0).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using h0)
  have hd : (h : ℚ) / ((B : ℚ) * C) = (κ : ℚ) / α := by
    rw [hh]
    push_cast
    field_simp
    have he : (α : ℚ) * ((e : ℚ) + 1) = κ * C := by exact_mod_cast h2
    nlinarith [congrArg (fun z : ℚ => z * B) he]
  rw [oneArrow_coordinateMultiplicity A B C e h hA hB hh hnA hdC hAC, hc, hd]

end CanonicalRoots
