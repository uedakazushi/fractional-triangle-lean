import CanonicalRoots.BranchedNumericalReduction

noncomputable section
namespace CanonicalRoots

theorem primitive_ternary_gcd_perm (w : Fin 3 → ℕ)
    (hw : Finset.univ.gcd w = 1) (σ : Equiv.Perm (Fin 3)) :
    Nat.gcd (Nat.gcd (w (σ 0)) (w (σ 1))) (w (σ 2)) = 1 := by
  apply primitive_ternary_common_divisor w hw
  intro j
  obtain ⟨i, rfl⟩ := σ.surjective j
  fin_cases i
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  · exact Nat.gcd_dvd_right _ _

namespace Target

theorem ternary_permuted_coordinate_constraints {a : ℕ} (t : Target 3 a)
    (σ : Equiv.Perm (Fin 3)) :
    let A := t.presentation.weights (σ 0)
    let B := t.presentation.weights (σ 1)
    let C := t.presentation.weights (σ 2)
    let h := t.presentation.relationDegree
    Nat.gcd (Nat.gcd A B) C = 1 ∧ h = a + (A + B + C) ∧
      orderMassLinear (coordinateMultiplicity ![A,B,C] h) = 3 ∧
      (a : ℚ) * ((h : ℚ) / ((A : ℚ) * B * C)) - 1 +
        multipleSumLinear 1 (coordinateMultiplicity ![A,B,C] h) = 0 := by
  dsimp only
  have htup : ![t.presentation.weights (σ 0), t.presentation.weights (σ 1), t.presentation.weights (σ 2)] =
      t.presentation.weights ∘ σ := by funext i; fin_cases i <;> rfl
  have hcoord : coordinateMultiplicity
      ![t.presentation.weights (σ 0), t.presentation.weights (σ 1), t.presentation.weights (σ 2)]
        t.presentation.relationDegree =
      coordinateMultiplicity t.presentation.weights t.presentation.relationDegree := by
    rw [htup, coordinateMultiplicity_reindex]
  have hsum : t.presentation.weights (σ 0) + t.presentation.weights (σ 1) + t.presentation.weights (σ 2) =
      ∑ i, t.presentation.weights i := by
    simpa only [Fin.sum_univ_three] using Equiv.sum_comp σ t.presentation.weights
  have hprod : (t.presentation.weights (σ 0) : ℚ) * t.presentation.weights (σ 1) * t.presentation.weights (σ 2) =
      ∏ i, (t.presentation.weights i : ℚ) := by
    simpa only [Fin.prod_univ_three] using Equiv.prod_comp σ (fun i => (t.presentation.weights i : ℚ))
  refine ⟨primitive_ternary_gcd_perm _ t.weights_gcd_eq_one σ, ?_, ?_, ?_⟩
  · rw [hsum]; exact t.relationDegree_eq_add_sum_weights
  · rw [hcoord]; exact t.coordinateMultiplicity_mass
  · rw [hcoord, hprod]; exact t.coordinateMultiplicity_defect

/-- A branched numerical support of an actual Target has a pure outside vertex. -/
theorem ternary_branched_pure_vertex {a : ℕ} (t : Target 3 a)
    (σ : Equiv.Perm (Fin 3)) (tag : Fin 7) (k : Fin 3 → ℕ)
    (hk : ∀ i, 2 ≤ k i) (htag : 5 ≤ tag.val)
    (haxis : ∀ i, axisWeight t.presentation.weights (σ i)
      (σ (threeAxisPattern tag i)) (k i) = t.presentation.relationDegree) :
    t.presentation.weights (σ 0) ∣ t.presentation.relationDegree ∨
      t.presentation.weights (σ 2) ∣ t.presentation.relationDegree := by
  have hcases : tag = 5 ∨ tag = 6 := by
    have hv : tag.val = 5 ∨ tag.val = 6 := by omega
    rcases hv with hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  have hends : threeAxisPattern tag 0 = 1 ∧ threeAxisPattern tag 2 = 1 := by
    rcases hcases with rfl | rfl <;> decide
  let A := t.presentation.weights (σ 0)
  let B := t.presentation.weights (σ 1)
  let C := t.presentation.weights (σ 2)
  let h := t.presentation.relationDegree
  have hA : 0 < A := t.presentation.weights_pos _
  have hB : 0 < B := t.presentation.weights_pos _
  have hC : 0 < C := t.presentation.weights_pos _
  have h0 : k 0 * A + B = h := by
    simpa [axisWeight, hends.1, σ.injective.eq_iff] using haxis 0
  have h2 : k 2 * C + B = h := by
    simpa [axisWeight, hends.2, σ.injective.eq_iff] using haxis 2
  obtain ⟨hprim, hdef, hmass, hzero⟩ := t.ternary_permuted_coordinate_constraints σ
  change Nat.gcd (Nat.gcd A B) C = 1 at hprim
  change h = a + (A + B + C) at hdef
  have hBh : B < h := by omega
  have hpAC : Nat.gcd A C ∣ h := t.ternary_pair_weight_gcd_dvd (σ 0) (σ 2)
    (σ.injective.ne (by decide))
  have hAC := primitive_arrow_opposite_coprime A B C h (k 0) hprim hpAC h0
  have hpure : A ∣ h ∨ C ∣ h := by
    rcases hcases with htag5 | htag6
    · have h1 : k 1 * B = h := by
        simpa [htag5, axisWeight, threeAxisPattern, σ.injective.eq_iff] using haxis 1
      exact branched_center_pure_forces_outside_pure A B C h (k 0) (k 2) hA hB hC hBh h0 h2
        (h1 ▸ dvd_mul_left _ _) hAC hmass
    · have h1 : k 1 * B + C = h := by
        simpa [htag6, axisWeight, threeAxisPattern, σ.injective.eq_iff] using haxis 1
      have hprim' : Nat.gcd (Nat.gcd B C) A = 1 := by
        simpa only [Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using hprim
      have hpBA : Nat.gcd B A ∣ h := t.ternary_pair_weight_gcd_dvd (σ 1) (σ 0)
        (σ.injective.ne (by decide))
      have hAB := (primitive_arrow_opposite_coprime B C A h (k 1) hprim' hpBA h1).symm
      exact branchedTwo_outside_pure_vertex A B C h a (k 0) (k 1) (k 2)
        hA hB hC hBh (hk 0) (hk 1) (hk 2) h0 h1 h2 hdef hAB hAC hmass hzero
  exact hpure

/-- Every actual ternary Target has the weights of one of I--V. This is a
numerical support theorem; it does not assert a coordinate change of its polynomial. -/
theorem ternary_five_axis_weights {a : ℕ} (t : Target 3 a) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 5, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧ ∀ i,
        axisWeight t.presentation.weights (σ i)
          (σ (threeAxisPattern ⟨tag.val, by omega⟩ i)) (k i) = t.presentation.relationDegree := by
  obtain ⟨σ, tag, k, hk, hc, _⟩ := t.ternary_five_or_branched_link
  have haxis (i : Fin 3) := axisWeight_of_support t.presentation.polynomial t.presentation.weights
    t.presentation.homogeneous (σ i) (σ (threeAxisPattern tag i)) (k i) (hc i)
  by_cases ht : tag.val < 5
  · exact ⟨σ, ⟨tag.val, ht⟩, k, hk, haxis⟩
  have htag : 5 ≤ tag.val := by omega
  have hpure := t.ternary_branched_pure_vertex σ tag k hk htag haxis
  have hdef' : (∑ i, t.presentation.weights i) < t.presentation.relationDegree := by
    have := t.relationDegree_eq_add_sum_weights
    have := t.parameter_input
    omega
  rcases hpure with hd | hd
  · obtain ⟨m, hm, he⟩ := pure_weight_exponent t.presentation.weights t.presentation.weights_pos hdef' (σ 0) hd
    exact numeric_branched_add_pure t.presentation.weights t.presentation.relationDegree σ tag htag k hk haxis 0 (by decide) m hm he
  · obtain ⟨m, hm, he⟩ := pure_weight_exponent t.presentation.weights t.presentation.weights_pos hdef' (σ 2) hd
    exact numeric_branched_add_pure t.presentation.weights t.presentation.relationDegree σ tag htag k hk haxis 2 (by decide) m hm he

end Target
end CanonicalRoots
