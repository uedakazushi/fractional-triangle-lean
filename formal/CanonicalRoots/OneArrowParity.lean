import CanonicalRoots.OneArrowScaledData

noncomputable section
namespace CanonicalRoots

/-- With scale two and one pair absent, the surviving order equals its exponent. -/
theorem one_vertex_scale_two_pair (A U S : ℕ) (hA : 2 ≤ A) (hS : 0 < S)
    (hmass : orderMassLinear (weightedOrderAtom A (A : ℚ)⁻¹ +
      weightedOrderAtom U ((2 : ℚ) / S)) = 3) : U = S := by
  obtain ⟨_, hm⟩ := one_vertex_mass_single_pair A U _ hA hmass
  have hS0 : (S : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hS
  field_simp at hm
  have : (U : ℚ) = S := by linarith
  exact_mod_cast this

/-- The gcd scale equation turns multiplicity two into the required even exponent. -/
theorem one_pair_scale_two_even (A U S e : ℕ) (hA : 2 ≤ A) (hS : 0 < S)
    (hmass : orderMassLinear (weightedOrderAtom A (A : ℚ)⁻¹ +
      weightedOrderAtom U ((2 : ℚ) / S)) = 3)
    (hgcd : 2 * U = S * Nat.gcd e 2) : 2 ∣ e := by
  have hUS := one_vertex_scale_two_pair A U S hA hS hmass
  have hg : Nat.gcd e 2 = 2 := by
    apply Nat.eq_of_mul_eq_mul_left hS
    rw [← hgcd, hUS]
    ring
  exact hg ▸ Nat.gcd_dvd_left e 2

end CanonicalRoots
