import CanonicalRoots.CoxRootResidue
import CanonicalRoots.RootCoordinateCongruence

namespace CanonicalRoots

/-- The chain lattice congruence gives a nonnegative exponent and a second congruence. -/
theorem chain_bounded_exponents {α γ d0 d1 d2 : ℕ} (hα : 0 < α) (hd0 : d0 < α)
    (hdiv : ((α * γ : ℕ) : ℤ) ∣ (d2 : ℤ) - d0 - α * d1) :
    ∃ c : ℕ, d2 = d0 + α * c ∧ d1 % γ = c % γ := by
  obtain ⟨k,hk⟩ := hdiv
  have hαdiv : (α : ℤ) ∣ (d2 : ℤ) - d0 := by
    refine ⟨(d1 : ℤ) + γ * k, ?_⟩
    push_cast at hk
    nlinarith
  have hm0 : d2 % α = d0 % α := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((d2 : ℤ) - d0) α).mpr hαdiv
    have heq : (d2 : ZMod α) = d0 := sub_eq_zero.mp (by simpa using hz)
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp heq
  have hd2 := congruence_bounded_decomposition hd0 hm0
  refine ⟨d2 / α, by omega, ?_⟩
  have hcdiv : (γ : ℤ) ∣ (d2 / α : ℕ) - (d1 : ℤ) := by
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ (show (α : ℤ) ≠ 0 by exact_mod_cast ne_of_gt hα)
    have hd2' : (d2 : ℤ) = α * (d2 / α : ℕ) + d0 := by exact_mod_cast hd2
    push_cast at hk
    nlinarith
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((d2 / α : ℕ) - (d1 : ℤ)) γ).mpr hcdiv
  have heq : ((d2 / α : ℕ) : ZMod γ) = d1 :=
    sub_eq_zero.mp (by simpa only [Int.cast_sub, Int.cast_natCast] using hz)
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp heq).symm

/-- Either the original Cox monomials suffice or a nonnegative power of Z^(alpha gamma) is needed. -/
theorem chain_exponent_cases {α γ d0 d1 d2 : ℕ} (hα : 0 < α) (hd0 : d0 < α)
    (hdiv : ((α * γ : ℕ) : ℤ) ∣ (d2 : ℤ) - d0 - α * d1) :
    (∃ b c : ℕ, d1 = γ * b + c ∧ d2 = d0 + α * c) ∨
      (∃ k : ℕ, d2 = d0 + α * d1 + (α * γ) * k) := by
  obtain ⟨c,hc,hmod⟩ := chain_bounded_exponents hα hd0 hdiv
  rcases le_total c d1 with hle | hle
  · obtain ⟨b,hb⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    exact Or.inl ⟨b,c,by omega,hc⟩
  · obtain ⟨k,hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod
    exact Or.inr ⟨k,by rw [hc,hk]; ring⟩

end CanonicalRoots
