import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

namespace CanonicalRoots

/-- Primitive positive weights turn rational proportionality into a positive
integer common factor. The proof uses the gcd of all scaled coordinates. -/
theorem primitive_weights_integer_scale {n : ℕ} (w W : Fin n → ℕ) (h H : ℕ)
    (hh : 0 < h) (hH : 0 < H) (hprim : Finset.univ.gcd w = 1)
    (hratio : ∀ i, H * w i = h * W i) :
    ∃ κ : ℕ, 0 < κ ∧ H = κ * h ∧ (∀ i, W i = κ * w i) ∧ Finset.univ.gcd W = κ := by
  have hd : h ∣ Finset.univ.gcd (fun i => H * w i) := by
    apply Finset.dvd_gcd
    intro i hi
    rw [hratio i]
    exact dvd_mul_right _ _
  simp only [Finset.gcd_mul_left, normalize_eq, hprim, mul_one] at hd
  obtain ⟨κ, hκ⟩ := hd
  have hκpos : 0 < κ := by nlinarith
  have hWi (i : Fin n) : W i = κ * w i := by
    apply Nat.eq_of_mul_eq_mul_left hh
    calc
      h * W i = H * w i := (hratio i).symm
      _ = h * (κ * w i) := by rw [hκ]; ring
  refine ⟨κ, hκpos, by simpa only [mul_comm] using hκ, hWi, ?_⟩
  have he : W = fun i => κ * w i := funext hWi
  rw [he, Finset.gcd_mul_left, hprim]
  simp

end CanonicalRoots
