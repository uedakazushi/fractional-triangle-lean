import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

noncomputable section
namespace CanonicalRoots

/-- An eventually equal linear-plus-periodic sequence has the same slope and
the same periodic part at every index, including before the equality threshold. -/
theorem linear_periodic_tail_unique (f g : ℕ → ℚ) (N : ℕ) (hN : 0 < N)
    (hf : Function.Periodic f N) (hg : Function.Periodic g N) (c d : ℚ)
    (h : ∃ M : ℕ, ∀ m ≥ M, (m : ℚ) * c + f m = (m : ℚ) * d + g m) :
    c = d ∧ f = g := by
  obtain ⟨M, hM⟩ := h
  have h0 := hM M (le_refl M)
  have h1 := hM (M + N) (by omega)
  rw [hf M, hg M, Nat.cast_add] at h1
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hcd : c = d := by nlinarith
  refine ⟨hcd, funext fun m => ?_⟩
  have hlarge : M ≤ m + M * N := by nlinarith
  have he := hM (m + M * N) hlarge
  have hf' : f (m + M * N) = f m := by simpa only [Nat.cast_id] using hf.nat_mul M m
  have hg' : g (m + M * N) = g m := by simpa only [Nat.cast_id] using hg.nat_mul M m
  rw [hf', hg', hcd] at he
  linarith

end CanonicalRoots
