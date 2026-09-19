import CanonicalRoots.OneArrowParity

noncomputable section
namespace CanonicalRoots.Target

/-- A saturated type-II table is primitive or has one of the two degree-two
exceptions. No support or classification hypothesis is added to the Target. -/
theorem ternary_oneArrow_scale_cases {a : ℕ} (t : Target 3 a)
    (α β γ κ : ℕ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (hκ : 0 < κ)
    (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .II α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .II α β γ i = (κ : ℤ) * t.presentation.weights (σ i))
    (hnA : ¬ t.presentation.weights (σ 0) ∣ t.presentation.relationDegree) :
    κ = 1 ∨ (κ = 2 ∧ α = 2 ∧ ∃ k : ℕ, 1 ≤ k ∧ β = 2 * k + 1) ∨
      (κ = 2 ∧ γ = 2 ∧ ∃ k : ℕ, 2 ≤ k ∧ β = 2 * k) := by
  let A := t.presentation.weights (σ 0)
  let B := t.presentation.weights (σ 1)
  let C := t.presentation.weights (σ 2)
  let h := t.presentation.relationDegree
  let e := β - 1
  have hA : 0 < A := t.presentation.weights_pos _
  have hB : 0 < B := t.presentation.weights_pos _
  have hC : 0 < C := t.presentation.weights_pos _
  have he : 0 < e := by dsimp [e]; omega
  have hβe : β = e + 1 := by dsimp [e]; omega
  have heInt : (e : ℤ) = (β : ℤ) - 1 := by dsimp [e]; omega
  have hA2 : 2 ≤ A := by
    by_contra hn
    have hz : A = 1 := by omega
    exact hnA (by change A ∣ h; simp [hz])
  have hhom := Cox.homogeneous_of_scaled_weights .II α β γ h κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) (by exact_mod_cast ne_of_gt hκ) hdeg hw
  have h0 : α * A + B = h := by
    have hh := hhom 0
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have h1 : β * B = h := by
    have hh := hhom 1
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have h2 : γ * C = h := by
    have hh := hhom 2
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have hs0 : γ * e = κ * A := by
    have hi : (γ : ℤ) * e = (κ : ℤ) * A := by simpa [Cox.weights, heInt, A] using hw 0
    exact_mod_cast hi
  have hs2 : α * (e + 1) = κ * C := by
    have hi : (α : ℤ) * β = (κ : ℤ) * C := by simpa [Cox.weights, C] using hw 2
    have hi' : α * β = κ * C := by exact_mod_cast hi
    simpa only [← hβe] using hi'
  have hprim := (t.ternary_permuted_coordinate_constraints σ).1
  have hAC := primitive_arrow_opposite_coprime A B C h α hprim
    (t.ternary_pair_weight_gcd_dvd (σ 0) (σ 2) (σ.injective.ne (by decide))) h0
  have hdata := oneArrow_scaled_coordinateMultiplicity A B C α γ e h κ hA hB hC (by omega) (by omega)
    (by rw [← hβe]; exact h1.symm) hnA (h2 ▸ dvd_mul_left _ _) hAC hs0 hs2
  have hmass := (t.ternary_permuted_coordinate_constraints σ).2.2.1
  rw [hdata] at hmass
  have htup : ![A,B,C] = t.presentation.weights ∘ σ := by funext i; fin_cases i <;> rfl
  have hcoord : coordinateMultiplicity ![A,B,C] h =
      coordinateMultiplicity t.presentation.weights h := by rw [htup, coordinateMultiplicity_reindex]
  have hsne (i : Fin 3) : Cox.signature .II α β γ i ≠ 0 := by
    have ha : (0 : ℤ) < α := by omega
    have hg : (0 : ℤ) < γ := by omega
    have hb : (0 : ℤ) < (β : ℤ) - 1 := by omega
    apply ne_of_gt
    fin_cases i <;> simp [Cox.signature] <;> positivity
  have hdef := t.ternary_scaled_defect_profile .II α β γ κ hκ σ hdeg hw hsne
  have hA0 : (A : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  have hk0 : (κ : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hκ
  have hcancel : (κ : ℚ) / (Cox.signature .II α β γ 1 : ℚ) = 1 / A := by
    have hs : (Cox.signature .II α β γ 1 : ℚ) = (κ : ℚ) * A := by
      have hh : Cox.signature .II α β γ 1 = (κ : ℤ) * A := by simpa [Cox.signature, Cox.weights, A] using hw 0
      exact_mod_cast hh
    rw [hs]
    field_simp
  simp only [Fin.sum_univ_three, hcancel] at hdef
  simp only [Cox.signature, Matrix.cons_val_zero, Matrix.cons_val_two, Int.cast_natCast] at hdef
  rw [← hcoord, hdata] at hdef
  have hs1 : α * γ = κ * B := by
    have hi : (α : ℤ) * γ = (κ : ℤ) * B := by simpa [Cox.weights, B] using hw 1
    exact_mod_cast hi
  have hpairs := oneArrow_scaled_pair_orders A B C α γ e κ hs0 hs1 hs2
  obtain hk | ⟨hk, ha, _, hv⟩ | ⟨hk, hg, hu, _⟩ :=
    oneArrow_scale_cases A (Nat.gcd A B) (Nat.gcd B C) α γ κ hA2
      (Nat.gcd_pos_of_pos_left B hA) (Nat.gcd_pos_of_pos_left C hB) hα hγ hκ hmass hdef
  · exact Or.inl hk
  · right; left
    have hz : weightedOrderAtom 1 (1 : ℚ) = 0 := by simp [weightedOrderAtom]
    have hm := hmass
    rw [hk, ha, hv] at hm
    norm_num only [Nat.cast_ofNat] at hm
    rw [hz, add_zero] at hm
    have hp : 2 * Nat.gcd A B = γ * Nat.gcd e 2 := by simpa only [hk, ha] using hpairs.1
    have heven := one_pair_scale_two_even A (Nat.gcd A B) γ e hA2 (by omega) hm hp
    obtain ⟨k, heq⟩ := heven
    exact ⟨hk, ha, k, by omega, by omega⟩
  · right; right
    have hz : weightedOrderAtom 1 (1 : ℚ) = 0 := by simp [weightedOrderAtom]
    have hm := hmass
    rw [hk, hg, hu] at hm
    norm_num only [Nat.cast_ofNat] at hm
    rw [hz, add_zero] at hm
    have hp : 2 * Nat.gcd B C = α * Nat.gcd β 2 := by
      simpa only [hk, hg, ← hβe, Nat.gcd_comm] using hpairs.2
    have heven := one_pair_scale_two_even A (Nat.gcd B C) α β hA2 (by omega) hm hp
    obtain ⟨k, heq⟩ := heven
    have hk2 : 2 ≤ k := by
      by_contra hn
      have hk1 : k = 1 := by omega
      have hb2 : β = 2 := by omega
      have hd := (t.ternary_permuted_coordinate_constraints σ).2.1
      have ha1 := t.parameter_input
      change h = a + (A + B + C) at hd
      rw [hb2] at h1
      rw [hg] at h2
      omega
    exact ⟨hk, hg, k, hk2, heq⟩

end CanonicalRoots.Target
