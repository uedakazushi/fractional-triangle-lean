import CanonicalRoots.CanonicalResidueFourier
import CanonicalRoots.PeriodicFourierBlock

noncomputable section
namespace CanonicalRoots

def residueFraction (p : ℕ) (σ : ℤ) (m : ℕ) : ℂ :=
  ((((m : ℤ) * σ) % p : ℤ) : ℂ) / (p : ℂ)

theorem residueFraction_periodic (p : ℕ) (σ : ℤ) :
    Function.Periodic (residueFraction p σ) p := by
  intro m
  unfold residueFraction
  congr 2
  simp [Nat.cast_add, add_mul, Int.add_emod]

/-- A coordinate's contribution on any common period is zero unless the chosen
root of unity is a root of its own period; the surviving value is independent of the common period. -/
theorem canonical_residue_common_period {p a k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (σ v : ℤ) (hσ : 0 ≤ σ) (hv : (a : ℤ) * σ + 1 = (p : ℤ) * v)
    (q : ℂ) (hq : q ^ (k * p) = 1) (hne : q ≠ 1) :
    -(1 / ((k * p : ℕ) : ℂ)) *
      (∑ j ∈ Finset.range (k * p), residueFraction p σ j * q ^ j) =
        if q ^ p = 1 then 1 / ((p : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0 := by
  by_cases hqp : q ^ p = 1
  · rw [ite_eq_left hqp, periodic_fourier_repeat _ _ _ (residueFraction_periodic p σ) q hqp]
    have hs := canonical_residue_fourier hp σ v hσ hv q hqp hne
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ((((j : ℤ) * σ) % p : ℤ) : ℂ) * q ^ j)] at hs
    calc
      _ = -(1 / (p : ℂ) ^ 2) *
          (∑ j ∈ Finset.range p, ((((j : ℤ) * σ) % p : ℤ) : ℂ) * q ^ j) := by
        simp only [residueFraction, div_mul_eq_mul_div, ← Finset.sum_div, Nat.cast_mul]
        have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
        have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
        field_simp
      _ = _ := hs
  · rw [ite_eq_right hqp, periodic_fourier_vanish _ _ _ (residueFraction_periodic p σ) q hq hqp,
      mul_zero]

end CanonicalRoots
