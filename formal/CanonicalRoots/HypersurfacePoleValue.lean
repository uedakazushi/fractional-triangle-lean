import CanonicalRoots.PolynomialPoleJets

noncomputable section
namespace CanonicalRoots
open Polynomial

theorem hypersurface_denominator_first_jet (A B C : ℕ) (q : ℂ) (hq : q ^ A = 1) :
    q * ((1 - (X : Polynomial ℂ) ^ A) * (1 - X ^ B) * (1 - X ^ C)).derivative.eval q =
      -(A : ℂ) * (1 - q ^ B) * (1 - q ^ C) := by
  rw [polynomial_three_factor_first_jet _ _ _ q (by simp [hq])]
  simp only [eval_sub, eval_one, eval_pow, eval_X]
  calc
    _ = (q * (1 - (X : Polynomial ℂ) ^ A).derivative.eval q) *
      (1 - q ^ B) * (1 - q ^ C) := by ring
    _ = _ := by rw [derivative_one_sub_X_pow_scaled, hq, mul_one]

theorem hypersurface_denominator_second_jet (A B C : ℕ) (q : ℂ)
    (hA : q ^ A = 1) (hB : q ^ B = 1) :
    q ^ 2 * ((1 - (X : Polynomial ℂ) ^ A) * (1 - X ^ B) * (1 - X ^ C)).derivative.derivative.eval q =
      2 * (A : ℂ) * B * (1 - q ^ C) := by
  rw [polynomial_three_factor_second_jet _ _ _ q (by simp [hA]) (by simp [hB])]
  simp only [eval_sub, eval_one, eval_pow, eval_X]
  calc
    _ = 2 * (q * (1 - (X : Polynomial ℂ) ^ A).derivative.eval q) *
      (q * (1 - (X : Polynomial ℂ) ^ B).derivative.eval q) * (1 - q ^ C) := by ring
    _ = _ := by rw [derivative_one_sub_X_pow_scaled, derivative_one_sub_X_pow_scaled, hA, hB]; ring

theorem period_denominator_first_jet (N : ℕ) (q : ℂ) (hN : q ^ N = 1) :
    q * ((1 - (X : Polynomial ℂ) ^ N) * (1 - X) ^ 2).derivative.eval q =
      -(N : ℂ) * (1 - q) ^ 2 := by
  have he : (1 - (X : Polynomial ℂ) ^ N) * (1 - X) ^ 2 =
      (1 - X ^ N) * (1 - X ^ 1) * (1 - X ^ 1) := by ring
  rw [he, hypersurface_denominator_first_jet N 1 1 q hN]
  simp only [pow_one]
  ring

/-- Algebraic pole value when exactly one weight vanishes at the root. -/
theorem hypersurface_simple_weight_pole (S : Polynomial ℂ) (A B C h N : ℕ)
    (ha : 0 < A) (hn : 0 < N) (q : ℂ)
    (hA : q ^ A = 1) (hB : q ^ B ≠ 1) (hC : q ^ C ≠ 1) (hN : q ^ N = 1) (hq : q ≠ 1)
    (hpoly : S * ((1 - X ^ A) * (1 - X ^ B) * (1 - X ^ C)) =
      (1 - X ^ h) * ((1 - X ^ N) * (1 - X) ^ 2)) :
    S.eval q / ((N : ℂ) * (1 - q) ^ 2) =
      (1 - q ^ h) / ((A : ℂ) * (1 - q ^ B) * (1 - q ^ C)) := by
  have hj := polynomial_first_jet_identity S
    ((1 - X ^ A) * (1 - X ^ B) * (1 - X ^ C))
    (1 - X ^ h) ((1 - X ^ N) * (1 - X) ^ 2) q hpoly (by simp [hA]) (by simp [hN])
  have he : S.eval q * (-(A : ℂ) * (1 - q ^ B) * (1 - q ^ C)) =
      (1 - q ^ h) * (-(N : ℂ) * (1 - q) ^ 2) := by
    rw [← hypersurface_denominator_first_jet A B C q hA,
      ← period_denominator_first_jet N q hN]
    simp only [eval_sub, eval_one, eval_pow, eval_X] at hj
    linear_combination q * hj
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hq0 : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hB0 : 1 - q ^ B ≠ 0 := sub_ne_zero.mpr (Ne.symm hB)
  have hC0 : 1 - q ^ C ≠ 0 := sub_ne_zero.mpr (Ne.symm hC)
  apply (div_eq_div_iff (mul_ne_zero hN0 (pow_ne_zero _ hq0))
    (mul_ne_zero (mul_ne_zero hA0 hB0) hC0)).mpr
  linear_combination -he

/-- Algebraic pole value when two weights and the relation degree vanish. -/
theorem hypersurface_pair_weight_pole (S : Polynomial ℂ) (A B C h N : ℕ)
    (ha : 0 < A) (hb : 0 < B) (hn : 0 < N) (q : ℂ)
    (hA : q ^ A = 1) (hB : q ^ B = 1) (hC : q ^ C ≠ 1)
    (hh : q ^ h = 1) (hN : q ^ N = 1) (hq : q ≠ 1)
    (hpoly : S * ((1 - X ^ A) * (1 - X ^ B) * (1 - X ^ C)) =
      (1 - X ^ h) * ((1 - X ^ N) * (1 - X) ^ 2)) :
    S.eval q / ((N : ℂ) * (1 - q) ^ 2) =
      (h : ℂ) / ((A : ℂ) * B * (1 - q ^ C)) := by
  have hD : ((1 - (X : Polynomial ℂ) ^ A) * (1 - X ^ B) * (1 - X ^ C)).derivative.eval q = 0 := by
    rw [polynomial_three_factor_first_jet _ _ _ q (by simp [hA])]
    simp [hB]
  have hj := polynomial_second_jet_identity S
    ((1 - X ^ A) * (1 - X ^ B) * (1 - X ^ C))
    (1 - X ^ h) ((1 - X ^ N) * (1 - X) ^ 2) q hpoly
    (by simp [hA]) hD (by simp [hh]) (by simp [hN])
  have hu : q * (1 - (X : Polynomial ℂ) ^ h).derivative.eval q = -(h : ℂ) := by
    rw [derivative_one_sub_X_pow_scaled, hh, mul_one]
  have he : S.eval q * (2 * (A : ℂ) * B * (1 - q ^ C)) =
      2 * (-(h : ℂ)) * (-(N : ℂ) * (1 - q) ^ 2) := by
    rw [← hypersurface_denominator_second_jet A B C q hA hB, ← hu,
      ← period_denominator_first_jet N q hN]
    linear_combination q ^ 2 * hj
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hq0 : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hC0 : 1 - q ^ C ≠ 0 := sub_ne_zero.mpr (Ne.symm hC)
  apply (div_eq_div_iff (mul_ne_zero hN0 (pow_ne_zero _ hq0))
    (mul_ne_zero (mul_ne_zero hA0 hB0) hC0)).mpr
  linear_combination he / 2

end CanonicalRoots
