import CanonicalRoots.CoxWeightProportional
import CanonicalRoots.PrimitiveWeightScale
import CanonicalRoots.TargetFiveWeights

namespace CanonicalRoots.Cox

/-- The Cox table is a positive integral multiple of any primitive solution of
its degree equations. The common factor is proved, not assumed to be one. -/
theorem primitive_weight_scale (kind : Kind) (α β γ : ℕ) (w : Fin 3 → ℕ) (h : ℕ)
    (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) (hh : 0 < h)
    (hprim : Finset.univ.gcd w = 1)
    (hhom : ∀ i, ∑ j, exponents kind α β γ i j * (w j : ℤ) = h) :
    ∃ κ : ℕ, 0 < κ ∧ degree kind α β γ = (κ : ℤ) * h ∧
      (∀ i, weights kind α β γ i = (κ : ℤ) * w i) ∧
      Finset.univ.gcd (fun i => (weights kind α β γ i).toNat) = κ := by
  let H := (degree kind α β γ).toNat
  let W := fun i => (weights kind α β γ i).toNat
  have hdeg : 0 < degree kind α β γ := degree_pos kind α β γ
    (by exact_mod_cast hα) (by exact_mod_cast hβ) (by exact_mod_cast hγ)
  have hweight (i : Fin 3) : 0 < weights kind α β γ i := weights_pos kind α β γ
    (by exact_mod_cast hα) (by exact_mod_cast hβ) (by exact_mod_cast hγ) i
  have hHcast : (H : ℤ) = degree kind α β γ := Int.toNat_of_nonneg (le_of_lt hdeg)
  have hWcast (i : Fin 3) : (W i : ℤ) = weights kind α β γ i := Int.toNat_of_nonneg (le_of_lt (hweight i))
  have hH : 0 < H := by omega
  have hratio : ∀ i, H * w i = h * W i := by
    intro i
    have he : (H : ℤ) * (w i : ℤ) = (h : ℤ) * (W i : ℤ) := by
      rw [hHcast, hWcast]
      exact weight_proportional kind α β γ h (fun i => (w i : ℤ)) (ne_of_gt hdeg) hhom i
    exact_mod_cast he
  obtain ⟨κ, hκ, hHκ, hWκ, hgcd⟩ := primitive_weights_integer_scale w W h H hh hH hprim hratio
  refine ⟨κ, hκ, ?_, ?_, hgcd⟩
  · rw [← hHcast, hHκ]
    norm_cast
  · intro i
    rw [← hWcast, hWκ]
    norm_cast

end CanonicalRoots.Cox

namespace CanonicalRoots

theorem primitive_weights_comp_perm (w : Fin 3 → ℕ) (hw : Finset.univ.gcd w = 1)
    (σ : Equiv.Perm (Fin 3)) : Finset.univ.gcd (w ∘ σ) = 1 := by
  apply primitive_ternary_common_divisor w hw
  intro j
  obtain ⟨i, rfl⟩ := σ.surjective j
  exact Finset.gcd_dvd (f := w ∘ σ) (Finset.mem_univ i)

/-- Every actual ternary Target has a Cox table whose weights and degree are
scaled by one positive integer. Primitive mutation is the remaining step. -/
theorem Target.ternary_scaled_cox_weights {a : ℕ} (t : Target 3 a) :
    ∃ kind : Cox.Kind, ∃ α β γ κ : ℕ, ∃ σ : Equiv.Perm (Fin 3),
      2 ≤ α ∧ 2 ≤ β ∧ 2 ≤ γ ∧ 0 < κ ∧
      Cox.degree kind α β γ = (κ : ℤ) * t.presentation.relationDegree ∧
      (∀ i, Cox.weights kind α β γ i = (κ : ℤ) * t.presentation.weights (σ i)) ∧
      Finset.univ.gcd (fun i => (Cox.weights kind α β γ i).toNat) = κ := by
  obtain ⟨σ, tag, k, hk, hweights⟩ := t.ternary_five_axis_weights
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
  exact ⟨axisKind tag, k 0, k 1, k 2, κ, σ, hk 0, hk 1, hk 2, hκ, hdeg, hw, hgcd⟩

end CanonicalRoots
