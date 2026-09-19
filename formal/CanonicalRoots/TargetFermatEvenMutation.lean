import CanonicalRoots.TargetCoxDefect
import CanonicalRoots.CoxWeightMutations

noncomputable section
namespace CanonicalRoots.Target

/-- The quadratic Fermat exception has an admissible primitive type-II table.
Positivity of the actual defect excludes the inadmissible exponent one. -/
theorem ternary_fermat_even_mutation {a : ℕ} (t : Target 3 a)
    (β γ : ℕ) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (heven : 2 ∣ β)
    (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .I 2 β γ = (2 : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .I 2 β γ i = (2 : ℤ) * t.presentation.weights (σ i)) :
    ∃ k : ℕ, 2 ≤ k ∧ Cox.degree .II k 2 γ = t.presentation.relationDegree ∧
      ∀ i, Cox.weights .II k 2 γ i = t.presentation.weights (σ (Equiv.swap 0 1 i)) := by
  obtain ⟨k, hb⟩ := heven
  have hdef := t.ternary_cox_defect .I 2 β γ 2 σ hdeg hw
  have hk : 2 ≤ k := by
    by_contra hn
    have hk1 : k = 1 := by omega
    have hb2 : β = 2 := by omega
    simp [Cox.defect, Cox.weights, Cox.degree, Fin.sum_univ_three, hb2] at hdef
    omega
  refine ⟨k, hk, ?_, ?_⟩
  · have hm := (Cox.fermat_to_oneArrow (k : ℤ) γ).1
    have hd := hdeg
    simp only [hb, Nat.cast_mul, Nat.cast_ofNat] at hd ⊢
    linarith
  · intro i
    have hm := (Cox.fermat_to_oneArrow (k : ℤ) γ).2 i
    have hi := hw (Equiv.swap 0 1 i)
    simp only [hb, Nat.cast_mul, Nat.cast_ofNat] at hi ⊢
    linarith

end CanonicalRoots.Target
