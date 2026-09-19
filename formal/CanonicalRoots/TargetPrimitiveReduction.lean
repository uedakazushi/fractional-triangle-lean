import CanonicalRoots.TargetTwoVertexPrimitive
import CanonicalRoots.NumericPureSaturation

noncomputable section
namespace CanonicalRoots.Target

/-- Every actual ternary Target has a saturated Cox weight table. A nontrivial
common factor can remain only in types I or II. -/
theorem ternary_saturated_scaled_cox_weights {a : ℕ} (t : Target 3 a) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 5, ∃ k : Fin 3 → ℕ, ∃ κ : ℕ,
      (∀ i, 2 ≤ k i) ∧ 0 < κ ∧
      Cox.degree (axisKind tag) (k 0) (k 1) (k 2) = (κ : ℤ) * t.presentation.relationDegree ∧
      (∀ i, Cox.weights (axisKind tag) (k 0) (k 1) (k 2) i = (κ : ℤ) * t.presentation.weights (σ i)) ∧
      Finset.univ.gcd (fun i => (Cox.weights (axisKind tag) (k 0) (k 1) (k 2) i).toNat) = κ ∧
      (∀ i, t.presentation.weights (σ i) ∣ t.presentation.relationDegree ↔
        i = threeAxisPattern ⟨tag.val, by omega⟩ i) ∧
      (tag.val < 2 ∨ κ = 1) := by
  obtain ⟨σ, tag, k, hk, hweights, hloop⟩ := t.ternary_five_saturated_weights
  have haxis (i : Fin 3) :
      axisWeight (t.presentation.weights ∘ σ) i (threeAxisPattern ⟨tag.val, by omega⟩ i) (k i) =
        t.presentation.relationDegree := by
    simpa only [axisWeight, σ.injective.eq_iff, Function.comp_apply] using hweights i
  have hhom := axisKind_homogeneous tag k (t.presentation.weights ∘ σ) t.presentation.relationDegree haxis
  have hh : 0 < t.presentation.relationDegree := by
    have := t.relationDegree_eq_add_sum_weights
    have := t.parameter_input
    omega
  obtain ⟨κ, hκ, hdeg, hw, hgcd⟩ := Cox.primitive_weight_scale (axisKind tag) (k 0) (k 1) (k 2)
    (t.presentation.weights ∘ σ) t.presentation.relationDegree (hk 0) (hk 1) (hk 2) hh
    (primitive_weights_comp_perm _ t.weights_gcd_eq_one σ) hhom
  refine ⟨σ, tag, k, κ, hk, hκ, hdeg, hw, hgcd, hloop, ?_⟩
  fin_cases tag
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · right
    apply t.ternary_twoCycle_scale_one (k 0) (k 1) (k 2) κ (hk 0) hκ σ
      (by simpa [axisKind] using hdeg) (by simpa [axisKind] using hw)
    · intro hd
      have he := (hloop 0).mp hd
      norm_num [threeAxisPattern] at he
    · intro hd
      have he := (hloop 1).mp hd
      norm_num [threeAxisPattern] at he
  · right
    apply t.ternary_chain_scale_one (k 0) (k 1) (k 2) κ (hk 2) hκ σ
      (by simpa [axisKind] using hdeg) (by simpa [axisKind] using hw)
    · intro hd
      have he := (hloop 0).mp hd
      norm_num [threeAxisPattern] at he
    · intro hd
      have he := (hloop 1).mp hd
      norm_num [threeAxisPattern] at he
  · right
    exact t.ternary_cycle_scale_one (k 0) (k 1) (k 2) κ hκ σ
      (by simpa [axisKind] using hdeg) (by simpa [axisKind] using hw)

end CanonicalRoots.Target
