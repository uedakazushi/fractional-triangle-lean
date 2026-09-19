import CanonicalRoots.CoordinateSignatureConstraints

noncomputable section
namespace CanonicalRoots

theorem half_sum_off_diagonal_three {V : Type*} [AddCommGroup V] [Module ℚ V]
    (F : Fin 3 → Fin 3 → V) (hF : ∀ i j, F i j = F j i) :
    (1 / 2 : ℚ) • (∑ i, ∑ j, if i = j then 0 else F i j) = F 0 1 + F 0 2 + F 1 2 := by
  simp only [Fin.sum_univ_three]
  norm_num only [Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_add, add_zero]
  rw [hF 1 0, hF 2 0, hF 2 1]
  module

/-- The ordered-pair definition reduces to the three unordered pairs. -/
theorem coordinateMultiplicity_three (A B C h : ℕ) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom A (if A ∣ h then 0 else (A : ℚ)⁻¹) +
      weightedOrderAtom B (if B ∣ h then 0 else (B : ℚ)⁻¹) +
      weightedOrderAtom C (if C ∣ h then 0 else (C : ℚ)⁻¹) +
      weightedOrderAtom (Nat.gcd A B)
        ((h : ℚ) / ((A : ℚ) * B) - (if A ∣ h then 0 else (A : ℚ)⁻¹) - (if B ∣ h then 0 else (B : ℚ)⁻¹)) +
      weightedOrderAtom (Nat.gcd A C)
        ((h : ℚ) / ((A : ℚ) * C) - (if A ∣ h then 0 else (A : ℚ)⁻¹) - (if C ∣ h then 0 else (C : ℚ)⁻¹)) +
      weightedOrderAtom (Nat.gcd B C)
        ((h : ℚ) / ((B : ℚ) * C) - (if B ∣ h then 0 else (B : ℚ)⁻¹) - (if C ∣ h then 0 else (C : ℚ)⁻¹)) := by
  classical
  let w : Fin 3 → ℕ := ![A,B,C]
  have hs (i j : Fin 3) :
      weightedOrderAtom (Nat.gcd (w i) (w j))
        ((h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j) =
      weightedOrderAtom (Nat.gcd (w j) (w i))
        ((h : ℚ) / ((w j : ℚ) * w i) - coordinateVertexCoefficient w h j - coordinateVertexCoefficient w h i) := by
    rw [Nat.gcd_comm]
    congr 1
    ring
  change (∑ i, weightedOrderAtom (w i) (coordinateVertexCoefficient w h i)) +
    (1 / 2 : ℚ) • (∑ i, ∑ j, if i = j then 0 else weightedOrderAtom (Nat.gcd (w i) (w j))
      ((h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j)) = _
  rw [half_sum_off_diagonal_three _ hs]
  simp only [Fin.sum_univ_three, w, coordinateVertexCoefficient, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  abel

/-- An arrow forces the opposite pair to be coprime, using the actual plane condition. -/
theorem primitive_arrow_opposite_coprime (A B C h k : ℕ)
    (hprimitive : Nat.gcd (Nat.gcd A B) C = 1)
    (hpair : Nat.gcd A C ∣ h) (harrow : k * A + B = h) : Nat.Coprime A C := by
  have hB : Nat.gcd A C ∣ B :=
    (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_left A C) k)).mpr (harrow ▸ hpair)
  have hd : Nat.gcd A C ∣ Nat.gcd (Nat.gcd A B) C :=
    Nat.dvd_gcd (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hB) (Nat.gcd_dvd_right _ _)
  rw [hprimitive] at hd
  exact Nat.dvd_one.mp hd

/-- When neither outside vertex admits a pure power, B1 has exactly these four
possible orders in the finite coordinate data. -/
theorem branchedOne_coordinateMultiplicity (A B C e h : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hh : h = (e + 1) * B)
    (hnA : ¬ A ∣ h) (hnC : ¬ C ∣ h) (hAC : Nat.Coprime A C) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom A (A : ℚ)⁻¹ + weightedOrderAtom C (C : ℚ)⁻¹ +
      weightedOrderAtom (Nat.gcd A B) ((e : ℚ) / A) +
      weightedOrderAtom (Nat.gcd B C) ((e : ℚ) / C) := by
  have hdB : B ∣ h := hh ▸ dvd_mul_left B (e + 1)
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  have hAB : (h : ℚ) / ((A : ℚ) * B) - (A : ℚ)⁻¹ = (e : ℚ) / A := by
    rw [hh]
    push_cast
    field_simp
    ring
  have hBC : (h : ℚ) / ((B : ℚ) * C) - (C : ℚ)⁻¹ = (e : ℚ) / C := by
    rw [hh]
    push_cast
    field_simp
    ring
  rw [coordinateMultiplicity_three]
  simp only [hnA, hnC, hdB, ↓reduceIte, sub_zero, zero_sub, zero_add,
    show Nat.gcd A C = 1 from hAC, hAB, hBC]
  simp [weightedOrderAtom]

end CanonicalRoots
