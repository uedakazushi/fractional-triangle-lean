import CanonicalRoots.TargetFermatData
import CanonicalRoots.TargetFermatEvenMutation
import CanonicalRoots.ThreePairOrientation

noncomputable section
namespace CanonicalRoots.Target

/-- Every Fermat weight table of an actual Target admits primitive Cox weights.
The quadratic and cubic exceptions are mutations of the numerical table. -/
theorem ternary_fermat_primitive_weights {a : ℕ} (t : Target 3 a)
    (α₀ β₀ γ₀ κ : ℕ) (hα₀ : 2 ≤ α₀) (hβ₀ : 2 ≤ β₀) (hγ₀ : 2 ≤ γ₀) (hκ : 0 < κ)
    (σ₀ : Equiv.Perm (Fin 3))
    (hdeg₀ : Cox.degree .I α₀ β₀ γ₀ = (κ : ℤ) * t.presentation.relationDegree)
    (hw₀ : ∀ i, Cox.weights .I α₀ β₀ γ₀ i = (κ : ℤ) * t.presentation.weights (σ₀ i)) :
    ∃ kind : Cox.Kind, ∃ α' β' γ' : ℕ, ∃ τ : Equiv.Perm (Fin 3),
      2 ≤ α' ∧ 2 ≤ β' ∧ 2 ≤ γ' ∧
      Cox.degree kind α' β' γ' = t.presentation.relationDegree ∧
      ∀ i, Cox.weights kind α' β' γ' i = t.presentation.weights (τ i) := by
  let k : Fin 3 → ℕ := ![α₀,β₀,γ₀]
  have hk (i : Fin 3) : 2 ≤ k i := by fin_cases i <;> simp [k, hα₀, hβ₀, hγ₀]
  obtain ⟨ρ, horient⟩ := three_pair_gcd_orientation (t.presentation.weights ∘ σ₀)
    (fun i => t.presentation.weights_pos _)
  let σ := ρ.trans σ₀
  let α := k (ρ 0)
  let β := k (ρ 1)
  let γ := k (ρ 2)
  have hα : 2 ≤ α := hk _
  have hβ : 2 ≤ β := hk _
  have hγ : 2 ≤ γ := hk _
  have hdeg : Cox.degree .I α β γ = (κ : ℤ) * t.presentation.relationDegree := by
    calc
      _ = Cox.degree .I α₀ β₀ γ₀ := by
        simpa [α, β, γ, k] using Cox.fermat_degree_reindex (fun i => (k i : ℤ)) ρ
      _ = _ := hdeg₀
  have hw (i : Fin 3) : Cox.weights .I α β γ i = (κ : ℤ) * t.presentation.weights (σ i) := by
    calc
      _ = Cox.weights .I α₀ β₀ γ₀ (ρ i) := by
        simpa [α, β, γ, k] using Cox.fermat_weights_reindex (fun i => (k i : ℤ))
          (fun j => by have := hk j; omega) ρ i
      _ = _ := hw₀ (ρ i)
  let A := t.presentation.weights (σ 0)
  let B := t.presentation.weights (σ 1)
  let C := t.presentation.weights (σ 2)
  let U := Nat.gcd A B
  let V := Nat.gcd A C
  let W := Nat.gcd B C
  change (2 ≤ U ∧ 2 ≤ V ∧ 2 ≤ W) ∨ (2 ≤ U ∧ 2 ≤ V ∧ W = 1) ∨
    (2 ≤ U ∧ V = 1 ∧ W = 1) ∨ (U = 1 ∧ V = 1 ∧ W = 1) at horient
  obtain ⟨hdata, hAB, hAC, hBC, hdef⟩ :=
    t.ternary_fermat_coordinate_data α β γ κ hα hβ hγ hκ σ hdeg hw
  change coordinateMultiplicity t.presentation.weights t.presentation.relationDegree =
    weightedOrderAtom U ((κ : ℚ) / γ) + weightedOrderAtom V ((κ : ℚ) / β) +
      weightedOrderAtom W ((κ : ℚ) / α) at hdata
  change κ * U = γ * Nat.gcd α β at hAB
  change κ * V = β * Nat.gcd α γ at hAC
  change κ * W = α * Nat.gcd β γ at hBC
  have hmass := t.coordinateMultiplicity_mass
  rw [hdata] at hmass hdef
  rcases horient with ⟨hU,hV,hW⟩ | ⟨hU,hV,hW⟩ | ⟨hU,hV,hW⟩ | ⟨hU,hV,hW⟩
  · simp [weightedOrderAtom, hU, hV, hW, map_add, multipleSumLinear_single] at hdef
    have hk1 : κ = 1 := by exact_mod_cast (show (κ : ℚ) = 1 by linarith)
    refine ⟨.I, α, β, γ, σ, hα, hβ, hγ, ?_, ?_⟩
    · simpa [hk1] using hdeg
    · intro i; simpa [hk1] using hw i
  · have hz (c : ℚ) : weightedOrderAtom 1 c = 0 := by simp [weightedOrderAtom]
    rw [hW, hz, add_zero] at hmass hdef
    obtain ⟨hk2, ha2, heven⟩ := pure_two_pair_scale_cases U V α β γ κ hU hV hα hβ hγ hκ hAB hAC hmass hdef
    have hd : Cox.degree .I 2 β γ = (2 : ℤ) * t.presentation.relationDegree := by simpa [hk2, ha2] using hdeg
    have hw' (i : Fin 3) : Cox.weights .I 2 β γ i = (2 : ℤ) * t.presentation.weights (σ i) := by simpa [hk2, ha2] using hw i
    rcases heven with hb | hg
    · obtain ⟨m, hm, hdm, hwm⟩ := t.ternary_fermat_even_mutation β γ hβ hγ hb σ hd hw'
      exact ⟨.II, m, 2, γ, (Equiv.swap 0 1).trans σ, hm, by omega, hγ, hdm, hwm⟩
    · let τ := (Equiv.swap (1 : Fin 3) 2).trans σ
      have hds : Cox.degree .I 2 γ β = (2 : ℤ) * t.presentation.relationDegree := by
        simpa [Cox.degree, mul_comm, mul_left_comm, mul_assoc] using hd
      have hws (i : Fin 3) : Cox.weights .I 2 γ β i = (2 : ℤ) * t.presentation.weights (τ i) := by
        have hr := Cox.fermat_weights_reindex (![2,(β : ℤ),(γ : ℤ)] : Fin 3 → ℤ)
          (by intro j; fin_cases j <;> simp <;> omega) (Equiv.swap 1 2) i
        have hi := hw' (Equiv.swap 1 2 i)
        have hr' : Cox.weights .I 2 γ β i = Cox.weights .I 2 β γ (Equiv.swap 1 2 i) := by
          simpa [Equiv.swap_apply_def] using hr
        exact hr'.trans hi
      obtain ⟨m, hm, hdm, hwm⟩ := t.ternary_fermat_even_mutation γ β hγ hβ hg τ hds hws
      exact ⟨.II, m, 2, β, (Equiv.swap 0 1).trans τ, hm, by omega, hβ, hdm, hwm⟩
  · have hz (c : ℚ) : weightedOrderAtom 1 c = 0 := by simp [weightedOrderAtom]
    rw [hV, hW, hz, hz, add_zero, add_zero] at hmass hdef
    have hακ : α ∣ κ := by
      have hd : α ∣ κ * W := hBC ▸ dvd_mul_right _ _
      simpa [hW] using hd
    have hβκ : β ∣ κ := by
      have hd : β ∣ κ * V := hAC ▸ dvd_mul_right _ _
      simpa [hV] using hd
    obtain ⟨hk3, ha3, hb3⟩ := pure_single_pair_scale_cases U α β γ κ hU hα hβ (by omega) hκ hAB hακ hβκ hmass hdef
    refine ⟨.III, 2, 2, γ, σ, by omega, by omega, hγ, ?_, ?_⟩
    · have hm := (Cox.fermat_to_twoCycle (γ : ℤ)).1
      have hd := hdeg
      simp only [hk3, ha3, hb3, Nat.cast_ofNat] at hd ⊢
      linarith
    · intro i
      have hm := (Cox.fermat_to_twoCycle (γ : ℤ)).2 i
      have hi := hw i
      simp only [hk3, ha3, hb3, Nat.cast_ofNat] at hi ⊢
      linarith
  · simp [hU, hV, hW, weightedOrderAtom] at hmass

end CanonicalRoots.Target
