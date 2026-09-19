import CanonicalRoots.TargetPrimitiveReduction
import CanonicalRoots.TargetOneArrowPrimitive
import CanonicalRoots.TargetFermatPrimitive

noncomputable section
namespace CanonicalRoots.Target

/-- Every actual ternary Target has a Cox table whose raw weights already equal
its primitive weights, up to a coordinate permutation. -/
theorem ternary_primitive_cox_weights {a : ℕ} (t : Target 3 a) :
    ∃ kind : Cox.Kind, ∃ α β γ : ℕ, ∃ σ : Equiv.Perm (Fin 3),
      2 ≤ α ∧ 2 ≤ β ∧ 2 ≤ γ ∧
      Cox.degree kind α β γ = t.presentation.relationDegree ∧
      ∀ i, Cox.weights kind α β γ i = t.presentation.weights (σ i) := by
  obtain ⟨σ, tag, k, κ, hk, hκ, hdeg, hw, _, hloop, hcases⟩ :=
    t.ternary_saturated_scaled_cox_weights
  rcases hcases with htag | hk1
  · have ht : tag = 0 ∨ tag = 1 := by omega
    rcases ht with ht | ht
    · subst tag
      exact t.ternary_fermat_primitive_weights (k 0) (k 1) (k 2) κ (hk 0) (hk 1) (hk 2) hκ σ
        (by simpa [axisKind] using hdeg) (by simpa [axisKind] using hw)
    · subst tag
      have hnA : ¬ t.presentation.weights (σ 0) ∣ t.presentation.relationDegree := by
        intro hd
        have he := (hloop 0).mp hd
        norm_num [threeAxisPattern] at he
      obtain ⟨kind, α, β, γ, hα, hβ, hγ, hd, hw'⟩ :=
        t.ternary_oneArrow_primitive_weights (k 0) (k 1) (k 2) κ (hk 0) (hk 1) (hk 2) hκ σ
          (by simpa [axisKind] using hdeg) (by simpa [axisKind] using hw) hnA
      exact ⟨kind, α, β, γ, σ, hα, hβ, hγ, hd, hw'⟩
  · refine ⟨axisKind tag, k 0, k 1, k 2, σ, hk 0, hk 1, hk 2, ?_, ?_⟩
    · simpa [hk1] using hdeg
    · intro i; simpa [hk1] using hw i

end CanonicalRoots.Target
