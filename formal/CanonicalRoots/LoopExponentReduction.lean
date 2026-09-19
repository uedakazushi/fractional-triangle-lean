import CanonicalRoots.LoopRootResidue

namespace CanonicalRoots

def LoopCongruence (α β γ x y z : ℕ) : Prop :=
  ((α * β * γ + 1 : ℕ) : ℤ) ∣ (γ : ℤ) * x - y - β * γ * z

theorem loop_congruence_rotate {α β γ x y z : ℕ} (h : LoopCongruence α β γ x y z) :
    LoopCongruence β γ α y z x := by
  obtain ⟨k,hk⟩ := h
  refine ⟨-(α : ℤ) * k - z, ?_⟩
  push_cast at hk ⊢
  linear_combination -(α : ℤ) * hk

/-- The small box contains no nonconstant monomial of loop-lattice degree. -/
theorem loop_small_box_zero {α β γ x y z : ℕ} (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (hx : x < β) (hy : y < γ) (hz : z < α) (h : LoopCongruence α β γ x y z) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx' : (x : ℤ) ≤ β - 1 := by omega
  have hy' : (y : ℤ) ≤ γ - 1 := by omega
  have hz' : (z : ℤ) ≤ α - 1 := by omega
  have hxmul := mul_le_mul_of_nonneg_left hx' (show 0 ≤ (γ : ℤ) by positivity)
  have hzmul := mul_le_mul_of_nonneg_left hz' (show 0 ≤ (β : ℤ) * γ by positivity)
  have hδ : 0 < (α : ℤ) * β * γ + 1 := by positivity
  have hlo : -((α : ℤ) * β * γ + 1) < (γ : ℤ) * x - y - β * γ * z := by
    nlinarith [show 0 ≤ (γ : ℤ) * x by positivity]
  have hhi : (γ : ℤ) * x - y - β * γ * z < (α : ℤ) * β * γ + 1 := by
    nlinarith [show 0 ≤ (β : ℤ) * γ * z by positivity]
  obtain ⟨k,hk⟩ := h
  push_cast at hk
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hkneg | hkzero | hkpos
    · have : k ≤ -1 := by omega
      nlinarith
    · exact hkzero
    · have : 1 ≤ k := by omega
      nlinarith
  have he : (γ : ℤ) * x - y - β * γ * z = 0 := by simpa [hk0] using hk
  have hz0 : z = 0 := by
    by_contra hn
    have : 1 ≤ z := by omega
    nlinarith
  have hx0 : x = 0 := by
    by_contra hn
    have : 1 ≤ x := by omega
    simp only [hz0, Nat.cast_zero, mul_zero, sub_zero] at he
    nlinarith
  exact ⟨hx0, by simp [hx0,hz0] at he; exact_mod_cast he, hz0⟩

/-- On a coordinate plane a nonconstant residual monomial has enough exponent for a Fermat reduction. -/
theorem loop_plane_large {α β γ x y : ℕ} (hγ : 0 < γ) (hx : 0 < x) (hy : y < γ)
    (h : LoopCongruence α β γ x y 0) : α * β + 1 ≤ x := by
  obtain ⟨k,hk⟩ := h
  push_cast at hk
  simp only [Int.ofNat_zero, mul_zero, sub_zero] at hk
  have hp : 0 < (γ : ℤ) * x - y := by
    have hx' : (1 : ℤ) ≤ x := by exact_mod_cast hx
    have hy' : (y : ℤ) < γ := by exact_mod_cast hy
    nlinarith
  have hδ : 0 < (α : ℤ) * β * γ + 1 := by positivity
  have hkpos : 1 ≤ k := by
    by_contra hn
    have : k ≤ 0 := by omega
    nlinarith
  have hlarge : (α : ℤ) * β < x := by nlinarith
  exact_mod_cast hlarge

/-- Every residual loop monomial either factors a Cox generator or admits a coordinate-plane reduction. -/
theorem loop_exponent_reduction_cases {α β γ x y z : ℕ}
    (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (h : LoopCongruence α β γ x y z) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨
    (β ≤ x ∧ 1 ≤ z) ∨ (1 ≤ x ∧ γ ≤ y) ∨ (1 ≤ y ∧ α ≤ z) ∨
    (z = 0 ∧ α * β + 1 ≤ x) ∨ (x = 0 ∧ β * γ + 1 ≤ y) ∨
    (y = 0 ∧ γ * α + 1 ≤ z) := by
  by_cases h0 : β ≤ x ∧ 1 ≤ z
  · exact Or.inr (Or.inl h0)
  by_cases h1 : 1 ≤ x ∧ γ ≤ y
  · exact Or.inr (Or.inr (Or.inl h1))
  by_cases h2 : 1 ≤ y ∧ α ≤ z
  · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
  have hrot := loop_congruence_rotate h
  have hrot2 := loop_congruence_rotate hrot
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · by_cases hz : z = 0
      · exact Or.inl ⟨hx,hy,hz⟩
      · have hh := loop_plane_large (by omega : 0 < β) (by omega : 0 < z)
          (show x < β by omega) (by simpa only [hy] using hrot2)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hy,hh⟩)))))
    · have hh := loop_plane_large (by omega : 0 < α) (by omega : 0 < y)
        (show z < α by omega) (by simpa only [hx] using hrot)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx,hh⟩)))))
  · by_cases hz : z = 0
    · have hh := loop_plane_large (by omega : 0 < γ) (by omega : 0 < x)
        (show y < γ by omega) (by simpa only [hz] using h)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz,hh⟩))))
    · by_cases hy : y = 0
      · have hh := loop_plane_large (by omega : 0 < β) (by omega : 0 < z)
          (show x < β by omega) (by simpa only [hy] using hrot2)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hy,hh⟩)))))
      · have hh := loop_small_box_zero hα hβ hγ (show x < β by omega)
          (show y < γ by omega) (show z < α by omega) h
        exact (hx hh.1).elim

end CanonicalRoots
