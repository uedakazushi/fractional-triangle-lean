import CanonicalRoots.RootPoleProfile

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem isolated_single_weight_pole_value {a h : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f)
    (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i) (hhom : IsWeightedHomogeneous w f h)
    (hdef : h = a + ∑ i, w i) (σ : Equiv.Perm (Fin 3)) (q : ℂ) (hq : q ≠ 0)
    (hA : q ^ w (σ 0) = 1) (hB : q ^ w (σ 1) ≠ 1) (hC : q ^ w (σ 2) ≠ 1) :
    (1 - q ^ (-(a : ℤ))) * ((1 - q ^ h) /
      ((w (σ 0) : ℂ) * (1 - q ^ w (σ 1)) * (1 - q ^ w (σ 2)))) =
      if w (σ 0) ∣ h then 0 else (w (σ 0) : ℂ)⁻¹ := by
  classical
  by_cases hdiv : w (σ 0) ∣ h
  · have hqh : q ^ h = 1 := by
      obtain ⟨k, hk⟩ := hdiv
      rw [hk, pow_mul, hA, one_pow]
    simp [hdiv, hqh]
  · simp only [hdiv, ↓reduceIte]
    have hs : (∑ i, w i) = w (σ 0) + w (σ 1) + w (σ 2) := by
      rw [← Equiv.sum_comp σ w, Fin.sum_univ_three]
    rw [hs] at hdef
    have hB0 : 1 - q ^ w (σ 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hB)
    have hC0 : 1 - q ^ w (σ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hC)
    obtain ⟨j, m, hm, hc⟩ := isolated_axis_coefficient f hf hlinear (σ 0)
    have he : m * w (σ 0) + w j = h := by
      simpa only [map_add, Finsupp.weight_single, smul_eq_mul, one_mul] using hhom hc
    obtain ⟨l, rfl⟩ := σ.surjective j
    fin_cases l
    · exact False.elim (hdiv (he ▸ dvd_add (dvd_mul_left _ _) (dvd_refl _)))
    · have hqh : q ^ h = q ^ w (σ 1) := by
        rw [← he, pow_add, pow_mul, pow_right_comm, hA, one_pow, one_mul]
        rfl
      have hn := negative_defect_power q hq hdef hA hqh
      rw [hn, hqh]
      field_simp
    · have hqh : q ^ h = q ^ w (σ 2) := by
        rw [← he, pow_add, pow_mul, pow_right_comm, hA, one_pow, one_mul]
        rfl
      have hdef' : h = a + (w (σ 0) + w (σ 2) + w (σ 1)) := by omega
      have hn := negative_defect_power q hq hdef' hA hqh
      rw [hn, hqh]
      field_simp

theorem Target.ternary_profile_single_weight {a e : ℕ} (t : Target 3 a) (he : 2 ≤ e)
    (σ : Equiv.Perm (Fin 3)) (hA : e ∣ t.presentation.weights (σ 0))
    (hB : ¬ e ∣ t.presentation.weights (σ 1)) (hC : ¬ e ∣ t.presentation.weights (σ 2)) :
    signatureDivisorProfile (List.ofFn t.signature : Multiset ℕ) e =
      if t.presentation.weights (σ 0) ∣ t.presentation.relationDegree then 0
      else (t.presentation.weights (σ 0) : ℚ)⁻¹ := by
  classical
  let q : ℂ := Complex.exp (2 * Real.pi * Complex.I / e)
  have hq : IsPrimitiveRoot q e := Complex.isPrimitiveRoot_exp e (by omega)
  have hp : ∀ i, 0 < t.signature i := fun i => by have := t.admissible.1 i; omega
  obtain ⟨N, hN, hd, heN⟩ := root_profile_common_period t.signature hp (by omega : 0 < e)
  have hqA := (hq.pow_eq_one_iff_dvd _).mpr hA
  have hqB : q ^ t.presentation.weights (σ 1) ≠ 1 := fun h => hB ((hq.pow_eq_one_iff_dvd _).mp h)
  have hqC : q ^ t.presentation.weights (σ 2) ≠ 1 := fun h => hC ((hq.pow_eq_one_iff_dvd _).mp h)
  have hc := t.presentation.single_weight_pole t.signature t.admissible t.parameter_input
    t.tau t.root_equation hN hd σ q ((hq.pow_eq_one_iff_dvd N).mpr heN)
    (hq.ne_one (by omega)) hqA hqB hqC
  change rootPoleCoefficient t.signature a q = _ at hc
  have hm := (rootPoleCoefficient_mul_defect t.signature hp t.tau t.root_equation q hq he).symm
  rw [hc, isolated_single_weight_pole_value t.presentation.polynomial t.presentation.isolated
    t.presentation.no_constant_or_linear t.presentation.weights t.presentation.weights_pos
    t.presentation.homogeneous t.relationDegree_eq_add_sum_weights σ q (hq.ne_zero (by omega))
    hqA hqB hqC] at hm
  apply Rat.cast_injective (α := ℂ)
  split_ifs with hdiv
  · simpa [hdiv] using hm
  · simpa [hdiv] using hm

end CanonicalRoots
