import CanonicalRoots.BranchedCoordinateData

noncomputable section
namespace CanonicalRoots

theorem branched_pair_mass_lower (A B e : ℕ) (hA : 0 < A) (hB : 0 < B)
    (he : 0 < e) (hd : A ∣ e * B) :
    1 ≤ (Nat.gcd A B : ℚ) * e / A := by
  have hd' : A ∣ e * Nat.gcd A B := dvd_mul_gcd_of_dvd_mul hd
  have hle : A ≤ e * Nat.gcd A B :=
    Nat.le_of_dvd (Nat.mul_pos he (Nat.gcd_pos_of_pos_left _ hA)) hd'
  apply (le_div_iff₀ (by exact_mod_cast hA : (0 : ℚ) < A)).mpr
  have hle' : (A : ℚ) ≤ (e : ℚ) * Nat.gcd A B := by exact_mod_cast hle
  simpa only [one_mul, mul_one, mul_comm] using hle'

theorem branchedOne_single_pair_forces_unit (A B C e : ℕ) (hA : 0 < A)
    (hdC : C ∣ e * B) (hBC : Nat.Coprime B C) (hAC : Nat.Coprime A C)
    (hmass : (Nat.gcd A B : ℚ) * e / A = 1) : C = 1 := by
  have heC : C ∣ e := hBC.symm.dvd_of_dvd_mul_right hdC
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have heq : Nat.gcd A B * e = A := by
    have hh := (div_eq_iff hA0).mp hmass
    norm_num only [one_mul] at hh
    exact_mod_cast hh
  have hdA : C ∣ A := heq ▸ dvd_mul_of_dvd_right heC (Nat.gcd A B)
  exact Nat.eq_one_of_dvd_coprimes hAC hdA (dvd_refl _)

/-- A B1 weight system with actual three-point mass must admit a pure outside
vertex. Thus its numerical support can be changed to one of I--V. -/
theorem branchedOne_has_pure_vertex (A B C e h : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (he : 0 < e)
    (hh : h = (e + 1) * B) (hdA : A ∣ e * B) (hdC : C ∣ e * B)
    (hAC : Nat.Coprime A C)
    (hmass : orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3) :
    A ∣ h ∨ C ∣ h := by
  by_contra hn
  push Not at hn
  have hA2 : 2 ≤ A := by
    by_contra h
    have h1 : A = 1 := by omega
    exact hn.1 (by simp [h1])
  have hC2 : 2 ≤ C := by
    by_contra h
    have h1 : C = 1 := by omega
    exact hn.2 (by simp [h1])
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  rw [branchedOne_coordinateMultiplicity A B C e h hA hB hC hh hn.1 hn.2 hAC] at hmass
  simp only [map_add, orderMassLinear_weightedOrderAtom, hA2, hC2, ↓reduceIte,
    mul_inv_cancel₀ hA0, mul_inv_cancel₀ hC0, ← mul_div_assoc] at hmass
  have hU := branched_pair_mass_lower A B e hA hB he hdA
  have hV : 1 ≤ (Nat.gcd B C : ℚ) * e / C := by
    simpa only [Nat.gcd_comm] using branched_pair_mass_lower C B e hC hB he hdC
  have hUpos := Nat.gcd_pos_of_pos_left B hA
  have hVpos := Nat.gcd_pos_of_pos_left C hB
  by_cases hU2 : 2 ≤ Nat.gcd A B
  · by_cases hV2 : 2 ≤ Nat.gcd B C
    · simp only [hU2, hV2, ↓reduceIte] at hmass
      linarith
    · have hV1 : Nat.Coprime B C := by change Nat.gcd B C = 1; omega
      simp only [hU2, hV2, ↓reduceIte, add_zero] at hmass
      have hc := branchedOne_single_pair_forces_unit A B C e hA hdC hV1 hAC (by linarith)
      omega
  · by_cases hV2 : 2 ≤ Nat.gcd B C
    · have hU1 : Nat.Coprime B A := Nat.coprime_comm.mpr (by change Nat.gcd A B = 1; omega)
      simp only [hU2, hV2, ↓reduceIte, add_zero] at hmass
      have hm : (Nat.gcd C B : ℚ) * e / C = 1 := by rw [Nat.gcd_comm]; linarith
      have ha := branchedOne_single_pair_forces_unit C B A e hC hdA hU1 hAC.symm hm
      omega
    · simp only [hU2, hV2, ↓reduceIte] at hmass
      norm_num at hmass

end CanonicalRoots
