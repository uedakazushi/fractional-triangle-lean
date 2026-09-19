import CanonicalRoots.PureCoordinateData

noncomputable section
namespace CanonicalRoots

theorem scaled_pair_mass (U κ S d : ℕ) (hS : 0 < S) (he : κ * U = S * d) :
    (U : ℚ) * ((κ : ℚ) / S) = d := by
  have hS0 : (S : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hS
  field_simp
  exact_mod_cast (by simpa only [Nat.mul_comm] using he)

/-- Two active pairs in the pure case force scale two and an even outer exponent. -/
theorem pure_two_pair_scale_cases (U V α β γ κ : ℕ)
    (hU : 2 ≤ U) (hV : 2 ≤ V) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (hκ : 0 < κ)
    (hAB : κ * U = γ * Nat.gcd α β) (hAC : κ * V = β * Nat.gcd α γ)
    (hmass : orderMassLinear (weightedOrderAtom U ((κ : ℚ) / γ) +
      weightedOrderAtom V ((κ : ℚ) / β)) = 3)
    (hdef : (κ : ℚ) - ((κ : ℚ) / α + (κ : ℚ) / β + (κ : ℚ) / γ) +
      multipleSumLinear 1 (weightedOrderAtom U ((κ : ℚ) / γ) +
        weightedOrderAtom V ((κ : ℚ) / β)) = 1) :
    κ = 2 ∧ α = 2 ∧ (2 ∣ β ∨ 2 ∣ γ) := by
  simp [weightedOrderAtom, hU, hV, map_add, multipleSumLinear_single] at hdef
  obtain ⟨hk, ha⟩ := nat_scale_missing_reciprocal κ α hκ hα (by linarith)
  simp only [map_add, orderMassLinear_weightedOrderAtom, hU, hV, ↓reduceIte] at hmass
  rw [scaled_pair_mass U κ γ _ (by omega) hAB, scaled_pair_mass V κ β _ (by omega) hAC] at hmass
  have hsum : Nat.gcd α β + Nat.gcd α γ = 3 := by exact_mod_cast hmass
  have hleB := Nat.gcd_le_left β (by omega : 0 < α)
  have hleC := Nat.gcd_le_left γ (by omega : 0 < α)
  have he : Nat.gcd α β = 2 ∨ Nat.gcd α γ = 2 := by omega
  refine ⟨hk, ha, ?_⟩
  rcases he with hb | hc
  · exact Or.inl (hb ▸ Nat.gcd_dvd_right α β)
  · exact Or.inr (hc ▸ Nat.gcd_dvd_right α γ)

/-- A single active pair forces the cubic exception I(3,3,gamma)/3. -/
theorem pure_single_pair_scale_cases (U α β γ κ : ℕ)
    (hU : 2 ≤ U) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 0 < γ) (hκ : 0 < κ)
    (hAB : κ * U = γ * Nat.gcd α β) (hακ : α ∣ κ) (hβκ : β ∣ κ)
    (hmass : orderMassLinear (weightedOrderAtom U ((κ : ℚ) / γ)) = 3)
    (hdef : (κ : ℚ) - ((κ : ℚ) / α + (κ : ℚ) / β + (κ : ℚ) / γ) +
      multipleSumLinear 1 (weightedOrderAtom U ((κ : ℚ) / γ)) = 1) :
    κ = 3 ∧ α = 3 ∧ β = 3 := by
  simp only [orderMassLinear_weightedOrderAtom, hU, ↓reduceIte] at hmass
  rw [scaled_pair_mass U κ γ _ hγ hAB] at hmass
  have hgcd : Nat.gcd α β = 3 := by exact_mod_cast hmass
  have hα3 : 3 ≤ α := hgcd ▸ Nat.gcd_le_left β (by omega : 0 < α)
  have hβ3 : 3 ≤ β := hgcd ▸ Nat.gcd_le_right α (by omega : 0 < β)
  have hαle : α ≤ κ := Nat.le_of_dvd hκ hακ
  have hβle : β ≤ κ := Nat.le_of_dvd hκ hβκ
  simp [weightedOrderAtom, hU, multipleSumLinear_single] at hdef
  have hboundα : (κ : ℚ) / α ≤ (κ : ℚ) / 3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    exact_mod_cast hα3
  have hboundβ : (κ : ℚ) / β ≤ (κ : ℚ) / 3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    exact_mod_cast hβ3
  have hk3 : κ ≤ 3 := by
    have : (κ : ℚ) ≤ 3 := by linarith
    exact_mod_cast this
  omega

end CanonicalRoots
