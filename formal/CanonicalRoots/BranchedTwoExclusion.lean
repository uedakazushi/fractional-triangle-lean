import CanonicalRoots.BranchedOneExclusion

noncomputable section
namespace CanonicalRoots

theorem branchedTwo_coordinateMultiplicity (A B C e h : ℕ)
    (hB : 0 < B) (hC : 0 < C) (hh : h = (e + 1) * B + C)
    (hnA : ¬ A ∣ h) (hnB : ¬ B ∣ h) (hnC : ¬ C ∣ h)
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom A (A : ℚ)⁻¹ + weightedOrderAtom B (B : ℚ)⁻¹ +
      weightedOrderAtom C (C : ℚ)⁻¹ + weightedOrderAtom (Nat.gcd B C) ((e : ℚ) / C) := by
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  have hBC : (h : ℚ) / ((B : ℚ) * C) - (B : ℚ)⁻¹ - (C : ℚ)⁻¹ = (e : ℚ) / C := by
    rw [hh]
    push_cast
    field_simp
    ring
  rw [coordinateMultiplicity_three]
  simp only [hnA, hnB, hnC, ↓reduceIte, show Nat.gcd A B = 1 from hAB,
    show Nat.gcd A C = 1 from hAC, hBC]
  simp [weightedOrderAtom]

theorem branchedTwo_mass_forces_coprime (A B C e h : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (he : 0 < e)
    (hh : h = (e + 1) * B + C) (hdC : C ∣ e * B)
    (hnA : ¬ A ∣ h) (hnB : ¬ B ∣ h) (hnC : ¬ C ∣ h)
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hmass : orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3) : Nat.Coprime B C := by
  have hA2 : 2 ≤ A := by
    by_contra hn
    have hv : A = 1 := by omega
    exact hnA (by simp [hv])
  have hB2 : 2 ≤ B := by
    by_contra hn
    have hv : B = 1 := by omega
    exact hnB (by simp [hv])
  have hC2 : 2 ≤ C := by
    by_contra hn
    have hv : C = 1 := by omega
    exact hnC (by simp [hv])
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  rw [branchedTwo_coordinateMultiplicity A B C e h hB hC hh hnA hnB hnC hAB hAC] at hmass
  simp only [map_add, orderMassLinear_weightedOrderAtom, hA2, hB2, hC2, ↓reduceIte,
    mul_inv_cancel₀ hA0, mul_inv_cancel₀ hB0, mul_inv_cancel₀ hC0, ← mul_div_assoc] at hmass
  have hW : 1 ≤ (Nat.gcd B C : ℚ) * e / C := by
    simpa only [Nat.gcd_comm] using branched_pair_mass_lower C B e hC hB he hdC
  have hWpos := Nat.gcd_pos_of_pos_left C hB
  change Nat.gcd B C = 1
  by_contra hn
  have hW2 : 2 ≤ Nat.gcd B C := by omega
  simp only [hW2, ↓reduceIte] at hmass
  linarith

/-- A rational identity for B2 after the three-point mass forces gcd(B,C)=1. -/
theorem branchedTwo_defect_identity (A B C α d : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (heq : α * A = (d * B + 1) * C) :
    (d * B * C - A) * ((d * B + 1) * C + B) / (A * B * C) - 1 +
      (1 / A + 1 / B + 1 / C) = d * (α - 1) + α / C - 1 := by
  have hα : α = (d * B + 1) * C / A := (eq_div_iff hA).mpr heq
  rw [hα]
  field_simp
  ring

theorem branchedTwo_defect_positive (A B C α d : ℚ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hα : 2 ≤ α) (hd : 1 ≤ d)
    (heq : α * A = (d * B + 1) * C) :
    0 < (d * B * C - A) * ((d * B + 1) * C + B) / (A * B * C) - 1 +
      (1 / A + 1 / B + 1 / C) := by
  rw [branchedTwo_defect_identity A B C α d (ne_of_gt hA) (ne_of_gt hB) (ne_of_gt hC) heq]
  have hm : 1 ≤ d * (α - 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ d) (by linarith : 0 ≤ α - 2)]
  have hp : 0 < α / C := div_pos (by linarith) hC
  linarith

/-- The numerical B2 conditions of an actual Target force a pure vertex.
This is a weight statement and does not assume a coordinate change of the polynomial. -/
theorem branchedTwo_has_pure_vertex (A B C h a α β γ : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (h0 : α * A + B = h) (h1 : β * B + C = h) (h2 : γ * C + B = h)
    (hdef : h = a + (A + B + C)) (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hmass : orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3)
    (hzero : (a : ℚ) * ((h : ℚ) / ((A : ℚ) * B * C)) - 1 +
      multipleSumLinear 1 (coordinateMultiplicity ![A,B,C] h) = 0) :
    A ∣ h ∨ B ∣ h ∨ C ∣ h := by
  by_contra hn
  push Not at hn
  obtain ⟨e, he⟩ : ∃ e, β = e + 1 ∧ 0 < e := ⟨β - 1, by omega⟩
  have hh : h = (e + 1) * B + C := by simpa only [he.1] using h1.symm
  have hdC : C ∣ e * B := by
    have heq : e * B = (γ - 1) * C := by rw [he.1] at h1; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ γ)]
    rw [heq]
    exact dvd_mul_left _ _
  have hBC := branchedTwo_mass_forces_coprime A B C e h hA hB hC he.2 hh hdC
    hn.1 hn.2.1 hn.2.2 hAB hAC hmass
  have heC : C ∣ e := hBC.symm.dvd_of_dvd_mul_right hdC
  obtain ⟨d, hed⟩ := heC
  have hd : 1 ≤ d := by
    by_contra hn
    have hz : d = 0 := by omega
    simp [hz] at hed
    omega
  have hha : h = (d * B + 1) * C + B := by rw [hh, hed]; ring
  have hrel : α * A = (d * B + 1) * C := by omega
  have hA2 : 2 ≤ A := by
    by_contra hl
    have hv : A = 1 := by omega
    exact hn.1 (by simp [hv])
  have hB2 : 2 ≤ B := by
    by_contra hl
    have hv : B = 1 := by omega
    exact hn.2.1 (by simp [hv])
  have hC2 : 2 ≤ C := by
    by_contra hl
    have hv : C = 1 := by omega
    exact hn.2.2 (by simp [hv])
  rw [branchedTwo_coordinateMultiplicity A B C e h hB hC hh hn.1 hn.2.1 hn.2.2 hAB hAC] at hzero
  simp only [show Nat.gcd B C = 1 from hBC, weightedOrderAtom, hA2, hB2, hC2,
    show ¬ 2 ≤ 1 by omega, ↓reduceIte, add_zero, map_add, multipleSumLinear_single,
    one_dvd, ↓reduceIte, ← one_div] at hzero
  have haQ : (a : ℚ) = (d : ℚ) * B * C - A := by
    have heq : a + A = d * B * C := by nlinarith [hdef, hha]
    have heqQ : (a : ℚ) + A = (d : ℚ) * B * C := by exact_mod_cast heq
    linarith
  have hhQ : (h : ℚ) = ((d : ℚ) * B + 1) * C + B := by exact_mod_cast hha
  have hrelQ : (α : ℚ) * A = ((d : ℚ) * B + 1) * C := by exact_mod_cast hrel
  have hp := branchedTwo_defect_positive (A : ℚ) B C α d
    (by exact_mod_cast hA) (by exact_mod_cast hB) (by exact_mod_cast hC)
    (by exact_mod_cast hα) (by exact_mod_cast hd) hrelQ
  rw [haQ, hhQ, ← mul_div_assoc] at hzero
  linarith

end CanonicalRoots
