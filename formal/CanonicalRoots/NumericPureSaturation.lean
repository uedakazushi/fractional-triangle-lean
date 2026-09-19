import CanonicalRoots.TargetFiveWeights

noncomputable section
namespace CanonicalRoots

/-- Choose every available pure power before reducing the axis map to seven
patterns. Divisibility of h is then exactly the loop condition. -/
theorem numeric_seven_saturated (w : Fin 3 → ℕ) (h : ℕ) (hw : ∀ i, 0 < w i)
    (hdef : (∑ i, w i) < h) (j k : Fin 3 → ℕ)
    (jfin : ∀ i, j i < 3) (hk : ∀ i, 2 ≤ k i)
    (hdeg : ∀ i, axisWeight w i ⟨j i, jfin i⟩ (k i) = h) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 7, ∃ l : Fin 3 → ℕ,
      (∀ i, 2 ≤ l i) ∧
      (∀ i, axisWeight w (σ i) (σ (threeAxisPattern tag i)) (l i) = h) ∧
      ∀ i, w (σ i) ∣ h ↔ i = threeAxisPattern tag i := by
  classical
  have hex : ∀ i, ∃ j' : Fin 3, ∃ k' : ℕ, 2 ≤ k' ∧ axisWeight w i j' k' = h ∧
      (j' = i ↔ w i ∣ h) := by
    intro i
    by_cases hd : w i ∣ h
    · obtain ⟨m, hm, he⟩ := pure_weight_exponent w hw hdef i hd
      exact ⟨i, m, hm, by simpa [axisWeight] using he, by simp [hd]⟩
    · refine ⟨⟨j i, jfin i⟩, k i, hk i, hdeg i, ?_⟩
      constructor
      · intro he
        have hh : k i * w i = h := by simpa [axisWeight, he] using hdeg i
        exact False.elim (hd (hh ▸ dvd_mul_left _ _))
      · intro hh
        exact False.elim (hd hh)
  choose f l hl haxis hloop using hex
  obtain ⟨σ, tag, hσ⟩ := three_axis_map_seven_cases f
  refine ⟨σ, tag, l ∘ σ, fun i => hl (σ i), ?_, ?_⟩
  · intro i
    change axisWeight w (σ i) (σ (threeAxisPattern tag i)) (l (σ i)) = h
    rw [← hσ i]
    exact haxis (σ i)
  · intro i
    have he := hloop (σ i)
    rw [hσ i] at he
    simpa only [σ.injective.eq_iff, eq_comm] using he.symm

/-- Strengthened five-type reduction: every weight dividing h is a loop.
This removes avoidable pure-power cases from the later primitive mutation. -/
theorem Target.ternary_five_saturated_weights {a : ℕ} (t : Target 3 a) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 5, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧
      (∀ i, axisWeight t.presentation.weights (σ i)
        (σ (threeAxisPattern ⟨tag.val, by omega⟩ i)) (k i) = t.presentation.relationDegree) ∧
      ∀ i, t.presentation.weights (σ i) ∣ t.presentation.relationDegree ↔
        i = threeAxisPattern ⟨tag.val, by omega⟩ i := by
  have hdef : (∑ i, t.presentation.weights i) < t.presentation.relationDegree := by
    have := t.relationDegree_eq_add_sum_weights
    have := t.parameter_input
    omega
  choose j k hk hc using isolated_positive_defect_axis_support t.presentation.polynomial
    t.presentation.isolated t.presentation.no_constant_or_linear t.presentation.weights t.presentation.homogeneous hdef
  have hdeg (i : Fin 3) := axisWeight_of_support t.presentation.polynomial t.presentation.weights
    t.presentation.homogeneous i (j i) (k i) (hc i)
  obtain ⟨σ, tag, l, hl, haxis, hloop⟩ := numeric_seven_saturated t.presentation.weights
    t.presentation.relationDegree t.presentation.weights_pos hdef (fun i => (j i).val) k
    (fun i => (j i).isLt) hk hdeg
  by_cases ht : tag.val < 5
  · exact ⟨σ, ⟨tag.val, ht⟩, l, hl, haxis, hloop⟩
  have htag : 5 ≤ tag.val := by omega
  have hends : threeAxisPattern tag 0 = 1 ∧ threeAxisPattern tag 2 = 1 := by
    have hf : ∀ tag : Fin 7, 5 ≤ tag.val → threeAxisPattern tag 0 = 1 ∧ threeAxisPattern tag 2 = 1 := by
      decide +kernel
    exact hf tag htag
  rcases t.ternary_branched_pure_vertex σ tag l hl htag haxis with hd | hd
  · have he := (hloop 0).mp hd
    rw [hends.1] at he
    norm_num at he
  · have he := (hloop 2).mp hd
    rw [hends.2] at he
    norm_num at he

end CanonicalRoots
