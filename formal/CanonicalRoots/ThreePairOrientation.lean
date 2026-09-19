import CanonicalRoots.PureCoordinateData

namespace CanonicalRoots

/-- Orient the graph of nontrivial pair gcds by one of three coordinate swaps. -/
theorem three_pair_gcd_orientation (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ σ : Equiv.Perm (Fin 3),
      (2 ≤ Nat.gcd (w (σ 0)) (w (σ 1)) ∧ 2 ≤ Nat.gcd (w (σ 0)) (w (σ 2)) ∧
        2 ≤ Nat.gcd (w (σ 1)) (w (σ 2))) ∨
      (2 ≤ Nat.gcd (w (σ 0)) (w (σ 1)) ∧ 2 ≤ Nat.gcd (w (σ 0)) (w (σ 2)) ∧
        Nat.gcd (w (σ 1)) (w (σ 2)) = 1) ∨
      (2 ≤ Nat.gcd (w (σ 0)) (w (σ 1)) ∧ Nat.gcd (w (σ 0)) (w (σ 2)) = 1 ∧
        Nat.gcd (w (σ 1)) (w (σ 2)) = 1) ∨
      (Nat.gcd (w (σ 0)) (w (σ 1)) = 1 ∧ Nat.gcd (w (σ 0)) (w (σ 2)) = 1 ∧
        Nat.gcd (w (σ 1)) (w (σ 2)) = 1) := by
  have hp01 : 0 < Nat.gcd (w 0) (w 1) := Nat.gcd_pos_of_pos_left _ (hw 0)
  have hp02 : 0 < Nat.gcd (w 0) (w 2) := Nat.gcd_pos_of_pos_left _ (hw 0)
  have hp12 : 0 < Nat.gcd (w 1) (w 2) := Nat.gcd_pos_of_pos_left _ (hw 1)
  by_cases h01 : 2 ≤ Nat.gcd (w 0) (w 1)
  · by_cases h02 : 2 ≤ Nat.gcd (w 0) (w 2)
    · by_cases h12 : 2 ≤ Nat.gcd (w 1) (w 2)
      · exact ⟨Equiv.refl _, Or.inl ⟨h01, h02, h12⟩⟩
      · have he12 : Nat.gcd (w 1) (w 2) = 1 := by omega
        exact ⟨Equiv.refl _, Or.inr (Or.inl ⟨h01, h02, he12⟩)⟩
    · have he02 : Nat.gcd (w 0) (w 2) = 1 := by omega
      by_cases h12 : 2 ≤ Nat.gcd (w 1) (w 2)
      · refine ⟨Equiv.swap 0 1, Or.inr (Or.inl ?_)⟩
        simpa [Equiv.swap_apply_def, Nat.gcd_comm] using And.intro h01 (And.intro h12 he02)
      · have he12 : Nat.gcd (w 1) (w 2) = 1 := by omega
        exact ⟨Equiv.refl _, Or.inr (Or.inr (Or.inl ⟨h01, he02, he12⟩))⟩
  · have he01 : Nat.gcd (w 0) (w 1) = 1 := by omega
    by_cases h02 : 2 ≤ Nat.gcd (w 0) (w 2)
    · by_cases h12 : 2 ≤ Nat.gcd (w 1) (w 2)
      · refine ⟨Equiv.swap 0 2, Or.inr (Or.inl ?_)⟩
        simpa [Equiv.swap_apply_def, Nat.gcd_comm] using And.intro h12 (And.intro h02 he01)
      · have he12 : Nat.gcd (w 1) (w 2) = 1 := by omega
        refine ⟨Equiv.swap 1 2, Or.inr (Or.inr (Or.inl ?_))⟩
        simpa [Equiv.swap_apply_def, Nat.gcd_comm] using And.intro h02 (And.intro he01 he12)
    · have he02 : Nat.gcd (w 0) (w 2) = 1 := by omega
      by_cases h12 : 2 ≤ Nat.gcd (w 1) (w 2)
      · refine ⟨Equiv.swap 0 2, Or.inr (Or.inr (Or.inl ?_))⟩
        simpa [Equiv.swap_apply_def, Nat.gcd_comm] using And.intro h12 (And.intro he02 he01)
      · have he12 : Nat.gcd (w 1) (w 2) = 1 := by omega
        exact ⟨Equiv.refl _, Or.inr (Or.inr (Or.inr ⟨he01, he02, he12⟩))⟩

end CanonicalRoots
