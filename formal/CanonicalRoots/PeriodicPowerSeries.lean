import Mathlib

noncomputable section
namespace CanonicalRoots

theorem powerSeries_polynomial_of_eventually_zero (s : PowerSeries ℂ)
    (h : ∃ M : ℕ, ∀ m ≥ M, PowerSeries.coeff m s = 0) :
    ∃ P : Polynomial ℂ, (P : PowerSeries ℂ) = s := by
  obtain ⟨M, hM⟩ := h
  refine ⟨s.trunc M, ?_⟩
  ext m
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hm
  · rfl
  · exact (hM m (by omega)).symm

/-- A periodic coefficient sequence has its usual finite polynomial numerator. -/
theorem periodicPowerSeries_mul_one_sub {N : ℕ} (f : ℕ → ℂ)
    (hf : Function.Periodic f N) :
    PowerSeries.mk f * (1 - PowerSeries.X ^ N) =
      ((PowerSeries.mk f).trunc N : PowerSeries ℂ) := by
  ext m
  simp only [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hm : N ≤ m
  · have hp : f m = f (m - N) := by simpa only [Nat.sub_add_cancel hm] using hf (m - N)
    simp [hm, not_lt_of_ge hm, hp]
  · simp [hm, Nat.lt_of_not_ge hm]

/-- The coefficient sequence `m` represents `X/(1-X)^2`. -/
theorem linearPowerSeries_mul_one_sub_sq :
    (PowerSeries.mk fun m : ℕ => (m : ℂ)) * (1 - PowerSeries.X) ^ 2 = PowerSeries.X := by
  let L : PowerSeries ℂ := PowerSeries.mk fun m => (m : ℂ)
  have he : L * (1 - PowerSeries.X) ^ 2 =
      L - (L * PowerSeries.X ^ 1 + L * PowerSeries.X ^ 1) + L * PowerSeries.X ^ 2 := by ring
  change L * (1 - PowerSeries.X) ^ 2 = _
  rw [he]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', L, PowerSeries.coeff_mk,
    PowerSeries.coeff_X]
  rcases m with _ | _ | m
  · simp
  · simp
  · simp only [show 1 ≤ m + 2 by omega, show 2 ≤ m + 2 by omega,
      ite_eq_left, show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega,
      show m + 2 ≠ 1 by omega, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring

/-- Finite changes to an eventual linear-plus-periodic sequence contribute a polynomial. -/
theorem eventual_linear_periodic_decomposition (s : PowerSeries ℂ) (μ : ℂ) (f : ℕ → ℂ)
    (h : ∃ M : ℕ, ∀ m ≥ M, PowerSeries.coeff m s = (m : ℂ) * μ + f m) :
    ∃ P : Polynomial ℂ,
      s = (P : PowerSeries ℂ) + PowerSeries.C μ * (PowerSeries.mk fun m : ℕ => (m : ℂ)) +
        PowerSeries.mk f := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨P, hP⟩ := powerSeries_polynomial_of_eventually_zero
    (s - PowerSeries.C μ * (PowerSeries.mk fun m : ℕ => (m : ℂ)) - PowerSeries.mk f)
    ⟨M, fun m hm => by simp [hM m hm, mul_comm]⟩
  exact ⟨P, by rw [hP]; ring⟩

/-- A polynomial numerator and its evaluation at a nontrivial period root.
No analytic convergence or limiting process is involved. -/
theorem eventual_linear_periodic_numerator {N : ℕ} (s : PowerSeries ℂ)
    (μ : ℂ) (f : ℕ → ℂ) (hf : Function.Periodic f N)
    (h : ∃ M : ℕ, ∀ m ≥ M, PowerSeries.coeff m s = (m : ℂ) * μ + f m) :
    ∃ S : Polynomial ℂ,
      (S : PowerSeries ℂ) = s * (1 - PowerSeries.X ^ N) * (1 - PowerSeries.X) ^ 2 ∧
      ∀ q : ℂ, q ^ N = 1 →
        S.eval q = (1 - q) ^ 2 * (∑ j ∈ Finset.range N, f j * q ^ j) := by
  obtain ⟨P, hP⟩ := eventual_linear_periodic_decomposition s μ f h
  let Q : Polynomial ℂ := (PowerSeries.mk f).trunc N
  refine ⟨P * (1 - Polynomial.X ^ N) * (1 - Polynomial.X) ^ 2 +
    Polynomial.C μ * Polynomial.X * (1 - Polynomial.X ^ N) + Q * (1 - Polynomial.X) ^ 2,
    ?_, ?_⟩
  · simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C]
    rw [hP]
    have hp := periodicPowerSeries_mul_one_sub f hf
    change PowerSeries.mk f * (1 - PowerSeries.X ^ N) = (Q : PowerSeries ℂ) at hp
    symm
    calc
      _ = (P : PowerSeries ℂ) * (1 - PowerSeries.X ^ N) * (1 - PowerSeries.X) ^ 2 +
          PowerSeries.C μ * ((PowerSeries.mk fun m : ℕ => (m : ℂ)) * (1 - PowerSeries.X) ^ 2) *
            (1 - PowerSeries.X ^ N) +
          (PowerSeries.mk f * (1 - PowerSeries.X ^ N)) * (1 - PowerSeries.X) ^ 2 := by ring
      _ = _ := by rw [linearPowerSeries_mul_one_sub_sq, hp]
  · intro q hq
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      hq, sub_self, mul_zero, zero_mul, zero_add]
    rw [mul_comm]
    congr 1
    simpa only [Q, Polynomial.eval₂_id, RingHom.id_apply, PowerSeries.coeff_mk] using
      (PowerSeries.eval₂_trunc_eq_sum_range q (RingHom.id ℂ) N (PowerSeries.mk f))

end CanonicalRoots
