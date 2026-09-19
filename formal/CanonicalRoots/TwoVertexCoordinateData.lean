import CanonicalRoots.CycleWeightPrimitivity

noncomputable section
namespace CanonicalRoots

theorem two_vertex_mass_recovers_atom (A B U : ℕ) (c : ℚ) (hA : 2 ≤ A) (hB : 2 ≤ B)
    (hmass : orderMassLinear (weightedOrderAtom A (A : ℚ)⁻¹ +
      weightedOrderAtom B (B : ℚ)⁻¹ + weightedOrderAtom U c) = 3) :
    2 ≤ U ∧ c = (U : ℚ)⁻¹ := by
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  simp only [map_add, orderMassLinear_weightedOrderAtom, hA, hB, ↓reduceIte,
    mul_inv_cancel₀ hA0, mul_inv_cancel₀ hB0] at hmass
  have hU : 2 ≤ U := by
    by_contra hn
    simp only [hn, ↓reduceIte] at hmass
    norm_num at hmass
  have hU0 : (U : ℚ) ≠ 0 := by exact_mod_cast (by omega : U ≠ 0)
  simp only [hU, ↓reduceIte] at hmass
  refine ⟨hU, ?_⟩
  apply mul_left_cancel₀ hU0
  rw [mul_inv_cancel₀ hU0]
  linarith

/-- Two arrows forming a two-cycle, and one pure vertex. -/
theorem twoCycle_coordinateMultiplicity (A B C e h : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hh : h = (e + 1) * A + B)
    (hnA : ¬ A ∣ h) (hnB : ¬ B ∣ h) (hdC : C ∣ h)
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom A (A : ℚ)⁻¹ + weightedOrderAtom B (B : ℚ)⁻¹ +
      weightedOrderAtom (Nat.gcd A B) ((e : ℚ) / B) := by
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hAB : (h : ℚ) / ((A : ℚ) * B) - (A : ℚ)⁻¹ - (B : ℚ)⁻¹ = (e : ℚ) / B := by
    rw [hh]
    push_cast
    field_simp
    ring
  rw [coordinateMultiplicity_three]
  simp only [hnA, hnB, hdC, ↓reduceIte, show Nat.gcd A C = 1 from hAC,
    show Nat.gcd B C = 1 from hBC, hAB]
  simp [weightedOrderAtom]

/-- A chain of two arrows ending at a pure vertex. -/
theorem chain_coordinateMultiplicity (A B C e h : ℕ)
    (hB : 0 < B) (hC : 0 < C) (hh : h = (e + 1) * C)
    (hnA : ¬ A ∣ h) (hnB : ¬ B ∣ h)
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom A (A : ℚ)⁻¹ + weightedOrderAtom B (B : ℚ)⁻¹ +
      weightedOrderAtom (Nat.gcd B C) ((e : ℚ) / B) := by
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  have hdC : C ∣ h := hh ▸ dvd_mul_left _ _
  have hBC : (h : ℚ) / ((B : ℚ) * C) - (B : ℚ)⁻¹ = (e : ℚ) / B := by
    rw [hh]
    push_cast
    field_simp
    ring
  rw [coordinateMultiplicity_three]
  simp only [hnA, hnB, hdC, ↓reduceIte, sub_zero, show Nat.gcd A B = 1 from hAB,
    show Nat.gcd A C = 1 from hAC, hBC]
  simp [weightedOrderAtom]

end CanonicalRoots
