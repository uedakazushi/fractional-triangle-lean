import CanonicalRoots.TwoVertexProfile

noncomputable section
namespace CanonicalRoots

/-- A single arrow and two pure vertices. The opposite pair is already coprime. -/
theorem oneArrow_coordinateMultiplicity (A B C e h : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hh : h = (e + 1) * B)
    (hnA : ¬ A ∣ h) (hdC : C ∣ h) (hAC : Nat.Coprime A C) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom A (A : ℚ)⁻¹ +
      weightedOrderAtom (Nat.gcd A B) ((e : ℚ) / A) +
      weightedOrderAtom (Nat.gcd B C) ((h : ℚ) / ((B : ℚ) * C)) := by
  have hdB : B ∣ h := hh ▸ dvd_mul_left _ _
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hAB : (h : ℚ) / ((A : ℚ) * B) - (A : ℚ)⁻¹ = (e : ℚ) / A := by
    rw [hh]
    push_cast
    field_simp
    ring
  rw [coordinateMultiplicity_three]
  simp only [hnA, hdB, hdC, ↓reduceIte, sub_zero,
    show Nat.gcd A C = 1 from hAC, hAB]
  simp [weightedOrderAtom]

/-- A single-vertex profile of mass three must have a nontrivial pair order. -/
theorem one_vertex_mass_pair_active (A U V : ℕ) (c d : ℚ) (hA : 2 ≤ A)
    (hmass : orderMassLinear (weightedOrderAtom A (A : ℚ)⁻¹ +
      weightedOrderAtom U c + weightedOrderAtom V d) = 3) : 2 ≤ U ∨ 2 ≤ V := by
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  by_contra hn
  have hn := not_or.mp hn
  simp only [map_add, orderMassLinear_weightedOrderAtom, hA, hn.1, hn.2,
    ↓reduceIte, mul_inv_cancel₀ hA0] at hmass
  norm_num at hmass

/-- If the second pair disappears, the first pair carries multiplicity two. -/
theorem one_vertex_mass_single_pair (A U : ℕ) (c : ℚ) (hA : 2 ≤ A)
    (hmass : orderMassLinear (weightedOrderAtom A (A : ℚ)⁻¹ + weightedOrderAtom U c) = 3) :
    2 ≤ U ∧ (U : ℚ) * c = 2 := by
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  simp only [map_add, orderMassLinear_weightedOrderAtom, hA, ↓reduceIte,
    mul_inv_cancel₀ hA0] at hmass
  have hU : 2 ≤ U := by
    by_contra hn
    simp only [hn, ↓reduceIte] at hmass
    norm_num at hmass
  refine ⟨hU, ?_⟩
  simp only [hU, ↓reduceIte] at hmass
  linarith

end CanonicalRoots
