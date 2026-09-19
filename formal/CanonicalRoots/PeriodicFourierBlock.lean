import CanonicalRoots.FiniteRootFourier
import Mathlib.Algebra.Ring.Periodic

noncomputable section
namespace CanonicalRoots

theorem periodic_fourier_block (f : ℕ → ℂ) (p : ℕ) (hf : Function.Periodic f p)
    (k : ℕ) (q : ℂ) :
    (∑ j ∈ Finset.range (k * p), f j * q ^ j) =
      (∑ j ∈ Finset.range p, f j * q ^ j) *
        (∑ j ∈ Finset.range k, (q ^ p) ^ j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hp : f (k * p + j) = f j := by
      simpa [mul_comm, add_comm] using (hf.nat_mul k j)
    rw [hp, pow_add, ← pow_mul]
    ring

theorem periodic_fourier_vanish (f : ℕ → ℂ) (p k : ℕ) (hf : Function.Periodic f p)
    (q : ℂ) (hq : q ^ (k * p) = 1) (hne : q ^ p ≠ 1) :
    (∑ j ∈ Finset.range (k * p), f j * q ^ j) = 0 := by
  rw [periodic_fourier_block f p hf k q, geom_sum_eq hne]
  have he : (q ^ p) ^ k = 1 := by rw [← pow_mul, mul_comm p k]; exact hq
  rw [he]
  simp

theorem periodic_fourier_repeat (f : ℕ → ℂ) (p k : ℕ) (hf : Function.Periodic f p)
    (q : ℂ) (hq : q ^ p = 1) :
    (∑ j ∈ Finset.range (k * p), f j * q ^ j) =
      (k : ℂ) * (∑ j ∈ Finset.range p, f j * q ^ j) := by
  rw [periodic_fourier_block f p hf k q, hq]
  simp [mul_comm]

end CanonicalRoots
