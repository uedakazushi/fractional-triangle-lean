import CanonicalRoots.CoxWeightNormalization

noncomputable section
namespace CanonicalRoots

theorem coordinate_vertex_mass (A h : ℕ) (hA : 0 < A) :
    orderMassLinear (weightedOrderAtom A (if A ∣ h then 0 else (A : ℚ)⁻¹)) =
      if A ∣ h then 0 else 1 := by
  by_cases hd : A ∣ h
  · simp [hd, weightedOrderAtom]
  · have hA2 : 2 ≤ A := by
      by_contra hn
      have he : A = 1 := by omega
      exact hd (by simp [he])
    have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
    simp [hd, orderMassLinear_weightedOrderAtom, hA2, hA0]

theorem coprime_coordinate_mass_forces_nondiv (A B C h : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (hmass : orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3) :
    ¬ A ∣ h ∧ ¬ B ∣ h ∧ ¬ C ∣ h := by
  rw [coordinateMultiplicity_three] at hmass
  have hz (c : ℚ) : weightedOrderAtom 1 c = 0 := by simp [weightedOrderAtom]
  simp only [show Nat.gcd A B = 1 from hAB, show Nat.gcd A C = 1 from hAC,
    show Nat.gcd B C = 1 from hBC, hz, add_zero, map_add,
    coordinate_vertex_mass A h hA, coordinate_vertex_mass B h hB, coordinate_vertex_mass C h hC] at hmass
  by_cases hdA : A ∣ h <;> by_cases hdB : B ∣ h <;> by_cases hdC : C ∣ h <;>
    simp_all <;> norm_num at *

/-- The defect calculation for a cycle uses only two degree relations and the
first raw Cox weight. No determinant formula is reproved here. -/
theorem cycle_defect_identity (A B C h a β γ κ : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hdef : h = a + (A + B + C)) (h1 : β * B + C = h) (h2 : γ * C + A = h)
    (hκ : κ * A = γ * (β - 1) + 1) :
    a * (h / (A * B * C)) - 1 + (1 / A + 1 / B + 1 / C) = κ - 1 := by
  have ha : a = h - A - B - C := by linarith
  have hb : β = (h - C) / B := (eq_div_iff hB).mpr (by linarith)
  have hc : γ = (h - A) / C := (eq_div_iff hC).mpr (by linarith)
  have hk : κ = (γ * (β - 1) + 1) / A := (eq_div_iff hA).mpr hκ
  rw [ha, hk, hb, hc]
  field_simp
  ring

/-- The cycle case of primitive mutation: its actual three-point/defect
constraints force the raw common factor to be one. -/
theorem cycle_weight_scale_one (A B C h a α β γ κ : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h0 : α * A + B = h) (h1 : β * B + C = h) (h2 : γ * C + A = h)
    (hprim : Nat.gcd (Nat.gcd A B) C = 1)
    (hpAB : Nat.gcd A B ∣ h) (hpAC : Nat.gcd A C ∣ h) (hpBC : Nat.gcd B C ∣ h)
    (hdef : h = a + (A + B + C))
    (hκ : (κ : ℚ) * A = (γ : ℚ) * ((β : ℚ) - 1) + 1)
    (hmass : orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3)
    (hzero : (a : ℚ) * ((h : ℚ) / ((A : ℚ) * B * C)) - 1 +
      multipleSumLinear 1 (coordinateMultiplicity ![A,B,C] h) = 0) : κ = 1 := by
  have hAC := primitive_arrow_opposite_coprime A B C h α hprim hpAC h0
  have hprimB : Nat.gcd (Nat.gcd B C) A = 1 := by
    simpa only [Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using hprim
  have hprimC : Nat.gcd (Nat.gcd C A) B = 1 := by
    simpa only [Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using hprim
  have hAB := (primitive_arrow_opposite_coprime B C A h β hprimB
    (by simpa only [Nat.gcd_comm] using hpAB) h1).symm
  have hBC := (primitive_arrow_opposite_coprime C A B h γ hprimC
    (by simpa only [Nat.gcd_comm] using hpBC) h2).symm
  obtain ⟨hnA, hnB, hnC⟩ := coprime_coordinate_mass_forces_nondiv A B C h hA hB hC hAB hAC hBC hmass
  have hA2 : 2 ≤ A := by
    by_contra hn
    have he : A = 1 := by omega
    exact hnA (by simp [he])
  have hB2 : 2 ≤ B := by
    by_contra hn
    have he : B = 1 := by omega
    exact hnB (by simp [he])
  have hC2 : 2 ≤ C := by
    by_contra hn
    have he : C = 1 := by omega
    exact hnC (by simp [he])
  rw [coordinateMultiplicity_three] at hzero
  simp only [show Nat.gcd A B = 1 from hAB, show Nat.gcd A C = 1 from hAC,
    show Nat.gcd B C = 1 from hBC, hnA, hnB, hnC, ↓reduceIte,
    weightedOrderAtom, hA2, hB2, hC2, show ¬ 2 ≤ 1 by omega, ↓reduceIte, add_zero,
    map_add, multipleSumLinear_single, one_dvd, ↓reduceIte, ← one_div] at hzero
  have heq := cycle_defect_identity (A : ℚ) B C h a β γ κ
    (by exact_mod_cast ne_of_gt hA) (by exact_mod_cast ne_of_gt hB) (by exact_mod_cast ne_of_gt hC)
    (by exact_mod_cast hdef) (by exact_mod_cast h1) (by exact_mod_cast h2) hκ
  rw [hzero] at heq
  have : (κ : ℚ) = 1 := by linarith
  exact_mod_cast this

end CanonicalRoots
