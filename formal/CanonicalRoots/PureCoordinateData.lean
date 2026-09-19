import CanonicalRoots.OneArrowScaleCases

noncomputable section
namespace CanonicalRoots

/-- When all three vertices are pure, only the pair orders contribute. -/
theorem pure_coordinateMultiplicity (A B C h : ℕ) (hA : A ∣ h) (hB : B ∣ h) (hC : C ∣ h) :
    coordinateMultiplicity ![A,B,C] h =
      weightedOrderAtom (Nat.gcd A B) ((h : ℚ) / ((A : ℚ) * B)) +
      weightedOrderAtom (Nat.gcd A C) ((h : ℚ) / ((A : ℚ) * C)) +
      weightedOrderAtom (Nat.gcd B C) ((h : ℚ) / ((B : ℚ) * C)) := by
  rw [coordinateMultiplicity_three]
  simp [hA, hB, hC, weightedOrderAtom]

/-- A raw Fermat table gives both its normalized pair coefficients and the
integer multiplicities, by gcd scaling. -/
theorem fermat_scaled_pair (A B C α β γ κ h : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hγ : 0 < γ) (hκ : 0 < κ)
    (h0 : β * γ = κ * A) (h1 : α * γ = κ * B) (h2 : α * β = κ * C)
    (hh : α * A = h) :
    (h : ℚ) / ((A : ℚ) * B) = (κ : ℚ) / γ ∧
      κ * Nat.gcd A B = γ * Nat.gcd α β := by
  constructor
  · have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
    have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
    have hg0 : (γ : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hγ
    rw [← hh]
    push_cast
    field_simp
    have he : (α : ℚ) * γ = κ * B := by exact_mod_cast h1
    nlinarith [congrArg (fun z : ℚ => z * A) he]
  · rw [← Nat.gcd_mul_left, ← h0, ← h1, Nat.gcd_mul_right]
    rw [Nat.gcd_comm]
    ring

end CanonicalRoots
