import CanonicalRoots.TargetOneArrowCases
import CanonicalRoots.CoxWeightMutations

noncomputable section
namespace CanonicalRoots.Target

/-- Every saturated type-II table has primitive Cox weights, using the two
exceptional mutations when its original table has a common factor. -/
theorem ternary_oneArrow_primitive_weights {a : ℕ} (t : Target 3 a)
    (α β γ κ : ℕ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (hκ : 0 < κ)
    (σ : Equiv.Perm (Fin 3))
    (hdeg : Cox.degree .II α β γ = (κ : ℤ) * t.presentation.relationDegree)
    (hw : ∀ i, Cox.weights .II α β γ i = (κ : ℤ) * t.presentation.weights (σ i))
    (hnA : ¬ t.presentation.weights (σ 0) ∣ t.presentation.relationDegree) :
    ∃ kind : Cox.Kind, ∃ α' β' γ' : ℕ,
      2 ≤ α' ∧ 2 ≤ β' ∧ 2 ≤ γ' ∧
      Cox.degree kind α' β' γ' = t.presentation.relationDegree ∧
      ∀ i, Cox.weights kind α' β' γ' i = t.presentation.weights (σ i) := by
  obtain hk | ⟨hk, ha, k, hk1, hb⟩ | ⟨hk, hg, k, hk2, hb⟩ :=
    t.ternary_oneArrow_scale_cases α β γ κ hα hβ hγ hκ σ hdeg hw hnA
  · refine ⟨.II, α, β, γ, hα, hβ, hγ, ?_, ?_⟩
    · simpa [hk] using hdeg
    · intro i; simpa [hk] using hw i
  · refine ⟨.III, 2, k+1, γ, by omega, by omega, hγ, ?_, ?_⟩
    · have hm := (Cox.oneArrow_to_twoCycle (k : ℤ) γ).1
      have hd := hdeg
      simp only [ha, hb, hk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hd ⊢
      linarith
    · intro i
      have hm := (Cox.oneArrow_to_twoCycle (k : ℤ) γ).2 i
      have hi := hw i
      simp only [ha, hb, hk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hi ⊢
      linarith
  · refine ⟨.IV, α, k, 2, hα, hk2, by omega, ?_, ?_⟩
    · have hm := (Cox.oneArrow_to_chain (α : ℤ) k).1
      have hd := hdeg
      simp only [hg, hb, hk, Nat.cast_mul, Nat.cast_ofNat] at hd ⊢
      linarith
    · intro i
      have hm := (Cox.oneArrow_to_chain (α : ℤ) k).2 i
      have hi := hw i
      simp only [hg, hb, hk, Nat.cast_mul, Nat.cast_ofNat] at hi ⊢
      linarith

end CanonicalRoots.Target
