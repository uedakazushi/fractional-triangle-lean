import CanonicalRoots.TwoVertexProfile

noncomputable section
namespace CanonicalRoots.Target

/-- Type III is primitive when all available pure powers have already been selected. -/
theorem ternary_twoCycle_scale_one {a : ℕ} (t : Target 3 a)
    (α β γ κ : ℕ) (hα : 2 ≤ α) (hκ : 0 < κ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .III α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .III α β γ i = (κ : ℤ) * t.presentation.weights (σ i))
    (hnA : ¬ t.presentation.weights (σ 0) ∣ t.presentation.relationDegree)
    (hnB : ¬ t.presentation.weights (σ 1) ∣ t.presentation.relationDegree) : κ = 1 := by
  let A := t.presentation.weights (σ 0)
  let B := t.presentation.weights (σ 1)
  let C := t.presentation.weights (σ 2)
  let h := t.presentation.relationDegree
  let e := α - 1
  let U := Nat.gcd A B
  have hA : 0 < A := t.presentation.weights_pos _
  have hB : 0 < B := t.presentation.weights_pos _
  have he : 0 < e := by dsimp [e]; omega
  have hαe : α = e + 1 := by dsimp [e]; omega
  have heInt : (e : ℤ) = (α : ℤ) - 1 := by dsimp [e]; omega
  have hhom := Cox.homogeneous_of_scaled_weights .III α β γ h κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) (by exact_mod_cast ne_of_gt hκ) hdeg hw
  have h0 : α * A + B = h := by
    have hh := hhom 0
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have h1 : β * B + A = h := by
    have hh := hhom 1
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    have hh' : (β : ℤ) * B + A = h := by dsimp [A, B, h]; linarith
    exact_mod_cast hh'
  have h2 : γ * C = h := by
    have hh := hhom 2
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have hprim := (t.ternary_permuted_coordinate_constraints σ).1
  have hAC := primitive_arrow_opposite_coprime A B C h α hprim
    (t.ternary_pair_weight_gcd_dvd (σ 0) (σ 2) (σ.injective.ne (by decide))) h0
  have hprim' : Nat.gcd (Nat.gcd B A) C = 1 := by simpa only [Nat.gcd_comm] using hprim
  have hBC := primitive_arrow_opposite_coprime B A C h β hprim'
    (t.ternary_pair_weight_gcd_dvd (σ 1) (σ 2) (σ.injective.ne (by decide))) h1
  have hA2 : 2 ≤ A := by
    by_contra hn
    have hz : A = 1 := by omega
    exact hnA (by change A ∣ h; simp [hz])
  have hB2 : 2 ≤ B := by
    by_contra hn
    have hz : B = 1 := by omega
    exact hnB (by change B ∣ h; simp [hz])
  have hdata := twoCycle_coordinateMultiplicity A B C e h hA hB
    (by rw [← hαe]; exact h0.symm) hnA hnB (h2 ▸ dvd_mul_left _ _) hAC hBC
  obtain ⟨hU, hc, hprofile⟩ := t.reciprocal_profile_of_two_vertex_data σ U ((e : ℚ) / B) hA2 hB2 hdata
  have hSe : γ * e = κ * B := by
    have hi : (γ : ℤ) * e = (κ : ℤ) * B := by
      simpa [Cox.weights, heInt, B] using hw 1
    exact_mod_cast hi
  have hγU := reciprocal_pair_scale B U e γ κ hB (by omega) he hc hSe
  apply t.ternary_scale_one_of_signature_scale .III α β γ κ hκ σ hdeg hw ![B,A,U]
  · intro i; fin_cases i <;> simp [hA, hB, show 0 < U by omega]
  · intro i
    fin_cases i
    · simpa [Cox.signature, Cox.weights, B] using hw 1
    · simpa [Cox.signature, Cox.weights, A] using hw 0
    · change (γ : ℤ) = (κ : ℤ) * U
      exact_mod_cast hγU
  · simpa [Fin.sum_univ_three, A, B, add_comm, add_left_comm, add_assoc] using hprofile

/-- Type IV is primitive after selecting every available pure power. -/
theorem ternary_chain_scale_one {a : ℕ} (t : Target 3 a)
    (α β γ κ : ℕ) (hγ : 2 ≤ γ) (hκ : 0 < κ) (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .IV α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .IV α β γ i = (κ : ℤ) * t.presentation.weights (σ i))
    (hnA : ¬ t.presentation.weights (σ 0) ∣ t.presentation.relationDegree)
    (hnB : ¬ t.presentation.weights (σ 1) ∣ t.presentation.relationDegree) : κ = 1 := by
  let A := t.presentation.weights (σ 0)
  let B := t.presentation.weights (σ 1)
  let C := t.presentation.weights (σ 2)
  let h := t.presentation.relationDegree
  let e := γ - 1
  let U := Nat.gcd B C
  have hA : 0 < A := t.presentation.weights_pos _
  have hB : 0 < B := t.presentation.weights_pos _
  have hC : 0 < C := t.presentation.weights_pos _
  have he : 0 < e := by dsimp [e]; omega
  have hγe : γ = e + 1 := by dsimp [e]; omega
  have heInt : (e : ℤ) = (γ : ℤ) - 1 := by dsimp [e]; omega
  have hhom := Cox.homogeneous_of_scaled_weights .IV α β γ h κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) (by exact_mod_cast ne_of_gt hκ) hdeg hw
  have h0 : α * A + B = h := by
    have hh := hhom 0
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have h1 : β * B + C = h := by
    have hh := hhom 1
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have h2 : γ * C = h := by
    have hh := hhom 2
    simp [Cox.exponents, Fin.sum_univ_three] at hh
    exact_mod_cast hh
  have hprim := (t.ternary_permuted_coordinate_constraints σ).1
  have hAC := primitive_arrow_opposite_coprime A B C h α hprim
    (t.ternary_pair_weight_gcd_dvd (σ 0) (σ 2) (σ.injective.ne (by decide))) h0
  have hprim' : Nat.gcd (Nat.gcd B C) A = 1 := by
    simpa only [Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using hprim
  have hAB := (primitive_arrow_opposite_coprime B C A h β hprim'
    (t.ternary_pair_weight_gcd_dvd (σ 1) (σ 0) (σ.injective.ne (by decide))) h1).symm
  have hA2 : 2 ≤ A := by
    by_contra hn
    have hz : A = 1 := by omega
    exact hnA (by change A ∣ h; simp [hz])
  have hB2 : 2 ≤ B := by
    by_contra hn
    have hz : B = 1 := by omega
    exact hnB (by change B ∣ h; simp [hz])
  have hdata := chain_coordinateMultiplicity A B C e h hB hC
    (by rw [← hγe]; exact h2.symm) hnA hnB hAB hAC
  obtain ⟨hU, hc, hprofile⟩ := t.reciprocal_profile_of_two_vertex_data σ U ((e : ℚ) / B) hA2 hB2 hdata
  have hSe : α * e = κ * B := by
    have hi : (α : ℤ) * e = (κ : ℤ) * B := by
      simpa [Cox.weights, heInt, B] using hw 1
    exact_mod_cast hi
  have hαU := reciprocal_pair_scale B U e α κ hB (by omega) he hc hSe
  apply t.ternary_scale_one_of_signature_scale .IV α β γ κ hκ σ hdeg hw ![U,A,B]
  · intro i; fin_cases i <;> simp [hA, hB, show 0 < U by omega]
  · intro i
    fin_cases i
    · change (α : ℤ) = (κ : ℤ) * U
      exact_mod_cast hαU
    · simpa [Cox.signature, Cox.weights, A] using hw 0
    · simpa [Cox.signature, Cox.weights, B] using hw 1
  · simpa [Fin.sum_univ_three, A, B, add_comm, add_left_comm, add_assoc] using hprofile

end CanonicalRoots.Target
