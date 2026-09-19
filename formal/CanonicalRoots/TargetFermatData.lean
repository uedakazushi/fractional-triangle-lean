import CanonicalRoots.FermatCoxReindex
import CanonicalRoots.PureScaleCases

noncomputable section
namespace CanonicalRoots.Target

/-- Pair coefficients, integer pair multiplicities, and the scaled defect are
all consequences of an actual Target with a Fermat weight table. -/
theorem ternary_fermat_coordinate_data {a : ℕ} (t : Target 3 a)
    (α β γ κ : ℕ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (hκ : 0 < κ)
    (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .I α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .I α β γ i = (κ : ℤ) * t.presentation.weights (σ i)) :
    let A := t.presentation.weights (σ 0)
    let B := t.presentation.weights (σ 1)
    let C := t.presentation.weights (σ 2)
    coordinateMultiplicity t.presentation.weights t.presentation.relationDegree =
      weightedOrderAtom (Nat.gcd A B) ((κ : ℚ) / γ) +
      weightedOrderAtom (Nat.gcd A C) ((κ : ℚ) / β) +
      weightedOrderAtom (Nat.gcd B C) ((κ : ℚ) / α) ∧
    κ * Nat.gcd A B = γ * Nat.gcd α β ∧
    κ * Nat.gcd A C = β * Nat.gcd α γ ∧
    κ * Nat.gcd B C = α * Nat.gcd β γ ∧
    (κ : ℚ) - ((κ : ℚ) / α + (κ : ℚ) / β + (κ : ℚ) / γ) +
      multipleSumLinear 1 (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) = 1 := by
  let A := t.presentation.weights (σ 0)
  let B := t.presentation.weights (σ 1)
  let C := t.presentation.weights (σ 2)
  let h := t.presentation.relationDegree
  change coordinateMultiplicity t.presentation.weights h = _ ∧ _
  have hA : 0 < A := t.presentation.weights_pos _
  have hB : 0 < B := t.presentation.weights_pos _
  have hC : 0 < C := t.presentation.weights_pos _
  have hhom := Cox.homogeneous_of_scaled_weights .I α β γ h κ
    (fun i => (t.presentation.weights (σ i) : ℤ)) (by exact_mod_cast ne_of_gt hκ) hdeg hw
  have h0 : α * A = h := by
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
  have hs0 : β * γ = κ * A := by
    have hi : (β : ℤ) * γ = (κ : ℤ) * A := by simpa [Cox.weights, A] using hw 0
    exact_mod_cast hi
  have hs1 : α * γ = κ * B := by
    have hi : (α : ℤ) * γ = (κ : ℤ) * B := by simpa [Cox.weights, B] using hw 1
    exact_mod_cast hi
  have hs2 : α * β = κ * C := by
    have hi : (α : ℤ) * β = (κ : ℤ) * C := by simpa [Cox.weights, C] using hw 2
    exact_mod_cast hi
  have hab := fermat_scaled_pair A B C α β γ κ h hA hB (by omega) hκ hs0 hs1 hs2 h0
  have hac := fermat_scaled_pair A C B α γ β κ h hA hC (by omega) hκ
    (by simpa only [Nat.mul_comm] using hs0) hs2 hs1 h0
  have hbc := fermat_scaled_pair B C A β γ α κ h hB hC (by omega) hκ
    (by simpa only [Nat.mul_comm] using hs1) (by simpa only [Nat.mul_comm] using hs2) hs0 h1
  have hdata := pure_coordinateMultiplicity A B C h (h0 ▸ dvd_mul_left _ _)
    (h1 ▸ dvd_mul_left _ _) (h2 ▸ dvd_mul_left _ _)
  rw [hab.1, hac.1, hbc.1] at hdata
  have htup : ![A,B,C] = t.presentation.weights ∘ σ := by funext i; fin_cases i <;> rfl
  rw [htup, coordinateMultiplicity_reindex] at hdata
  refine ⟨hdata, hab.2, hac.2, hbc.2, ?_⟩
  have hsne (i : Fin 3) : Cox.signature .I α β γ i ≠ 0 := by
    fin_cases i <;> simp [Cox.signature] <;> omega
  have he := t.ternary_scaled_defect_profile .I α β γ κ hκ σ hdeg hw hsne
  simpa [Fin.sum_univ_three, Cox.signature] using he

end CanonicalRoots.Target
