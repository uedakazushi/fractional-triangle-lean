import CanonicalRoots.OneVertexCoordinateData
import CanonicalRoots.CoxScaledDefect

noncomputable section
namespace CanonicalRoots

/-- The one missing reciprocal in the defect forces the unique integer exception. -/
theorem nat_scale_missing_reciprocal (κ α : ℕ) (hκ : 0 < κ) (hα : 2 ≤ α)
    (he : (κ : ℚ) - (κ : ℚ) / α = 1) : κ = 2 ∧ α = 2 := by
  have hα0 : (α : ℚ) ≠ 0 := by exact_mod_cast (by omega : α ≠ 0)
  have hq : (κ : ℚ) * α = κ + α := by
    field_simp at he
    linarith
  have hn : κ * α = κ + α := by exact_mod_cast hq
  have hk2 : 2 ≤ κ := by
    by_contra hk
    have : κ = 1 := by omega
    simp [this] at hn
  have hprod : 0 ≤ ((κ : ℤ) - 2) * ((α : ℤ) - 2) :=
    mul_nonneg (by omega) (by omega)
  have hnz : (κ : ℤ) * α = κ + α := by exact_mod_cast hn
  have hkz : (2 : ℤ) ≤ κ := by exact_mod_cast hk2
  have haz : (2 : ℤ) ≤ α := by exact_mod_cast hα
  have hz : (κ : ℤ) = 2 ∧ (α : ℤ) = 2 := by constructor <;> nlinarith
  exact_mod_cast hz

/-- The single-vertex profile leaves precisely two nonprimitive possibilities.
This uses the actual mass and defect equations, not a classification premise. -/
theorem oneArrow_scale_cases (A U V α γ κ : ℕ)
    (hA : 2 ≤ A) (hU : 0 < U) (hV : 0 < V)
    (hα : 2 ≤ α) (hγ : 2 ≤ γ) (hκ : 0 < κ)
    (hmass : orderMassLinear (weightedOrderAtom A (A : ℚ)⁻¹ +
      weightedOrderAtom U ((κ : ℚ) / γ) + weightedOrderAtom V ((κ : ℚ) / α)) = 3)
    (hdef : (κ : ℚ) - ((κ : ℚ) / α + 1 / A + (κ : ℚ) / γ) +
      multipleSumLinear 1 (weightedOrderAtom A (A : ℚ)⁻¹ +
        weightedOrderAtom U ((κ : ℚ) / γ) + weightedOrderAtom V ((κ : ℚ) / α)) = 1) :
    κ = 1 ∨ (κ = 2 ∧ α = 2 ∧ 2 ≤ U ∧ V = 1) ∨
      (κ = 2 ∧ γ = 2 ∧ U = 1 ∧ 2 ≤ V) := by
  have hactive := one_vertex_mass_pair_active A U V _ _ hA hmass
  by_cases hU2 : 2 ≤ U
  · by_cases hV2 : 2 ≤ V
    · left
      simp [weightedOrderAtom, hA, hU2, hV2, map_add, multipleSumLinear_single] at hdef
      have : (κ : ℚ) = 1 := by linarith
      exact_mod_cast this
    · right; left
      have hV1 : V = 1 := by omega
      simp [weightedOrderAtom, hA, hU2, hV1, map_add, multipleSumLinear_single] at hdef
      obtain ⟨hk, ha⟩ := nat_scale_missing_reciprocal κ α hκ hα (by linarith)
      exact ⟨hk, ha, hU2, hV1⟩
  · right; right
    have hV2 : 2 ≤ V := hactive.resolve_left hU2
    have hU1 : U = 1 := by omega
    simp [weightedOrderAtom, hA, hU1, hV2, map_add, multipleSumLinear_single] at hdef
    obtain ⟨hk, hg⟩ := nat_scale_missing_reciprocal κ γ hκ hγ (by linarith)
    exact ⟨hk, hg, hU1, hV2⟩

end CanonicalRoots
