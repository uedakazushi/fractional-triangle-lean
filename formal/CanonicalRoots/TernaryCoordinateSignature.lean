import CanonicalRoots.CoordinateMultiplicity
import CanonicalRoots.RootVertexProfile

noncomputable section
namespace CanonicalRoots

theorem ternary_divisibility_cases (w : Fin 3 → ℕ) (e : ℕ) (hn : ¬ ∀ i, e ∣ w i) :
    (∀ i, ¬ e ∣ w i) ∨ ∃ σ : Equiv.Perm (Fin 3),
      (e ∣ w (σ 0) ∧ ¬ e ∣ w (σ 1) ∧ ¬ e ∣ w (σ 2)) ∨
      (e ∣ w (σ 0) ∧ e ∣ w (σ 1) ∧ ¬ e ∣ w (σ 2)) := by
  have h : ∀ b : Fin 3 → Bool, (¬ ∀ i, b i = true) →
      (∀ i, b i = false) ∨ ∃ r : Fin 6,
        (b (threeCoordinatePermutation r 0) = true ∧
          b (threeCoordinatePermutation r 1) = false ∧ b (threeCoordinatePermutation r 2) = false) ∨
        (b (threeCoordinatePermutation r 0) = true ∧
          b (threeCoordinatePermutation r 1) = true ∧ b (threeCoordinatePermutation r 2) = false) := by
    decide +kernel
  rcases h (fun i => decide (e ∣ w i)) (by simpa using hn) with h | ⟨r, h⟩
  · exact Or.inl (by simpa using h)
  · exact Or.inr ⟨threeCoordinatePermutation r, by simpa using h⟩

/-- The finite rational coordinate data equals the actual signature count divided
by the order. Positivity and integral multiplicities follow from this equality,
not from the definition of the coordinate data. -/
theorem Target.coordinateMultiplicity_eq_signature {a : ℕ} (t : Target 3 a) :
    coordinateMultiplicity t.presentation.weights t.presentation.relationDegree =
      signatureMultiplicity (List.ofFn t.signature : Multiset ℕ) := by
  apply finsupp_eq_of_multipleSum
  · intro r hr
    rw [coordinateMultiplicity_small _ _ r hr, signatureMultiplicity_apply]
    have hcount : (List.ofFn t.signature : Multiset ℕ).count r = 0 := by
      apply Multiset.count_eq_zero.mpr
      intro hm
      have hl : r ∈ List.ofFn t.signature := by simpa only [Multiset.mem_coe] using hm
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hl
      have := t.admissible.1 i
      omega
    change 0 = (((List.ofFn t.signature : Multiset ℕ).count r : ℚ) / (r : ℚ))
    rw [hcount]
    simp
  · intro e he
    have hnot : ¬ ∀ i, e ∣ t.presentation.weights i := by
      intro h
      have := primitive_ternary_common_divisor t.presentation.weights t.weights_gcd_eq_one e h
      omega
    change multipleSumLinear e (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) =
      signatureDivisorProfile (List.ofFn t.signature : Multiset ℕ) e
    rcases ternary_divisibility_cases t.presentation.weights e hnot with hn | ⟨σ, hs | hp⟩
    · rw [coordinateMultiplicity_profile_none _ t.presentation.weights_pos _ e he hn,
        t.ternary_profile_no_weight he hn]
    · rw [← coordinateMultiplicity_reindex _ _ σ]
      exact (coordinateMultiplicity_profile_single (t.presentation.weights ∘ σ)
        (fun i => t.presentation.weights_pos (σ i)) _ e he hs.1 hs.2.1 hs.2.2).trans
        (t.ternary_profile_single_weight he σ hs.1 hs.2.1 hs.2.2).symm
    · rw [← coordinateMultiplicity_reindex _ _ σ]
      exact (coordinateMultiplicity_profile_pair (t.presentation.weights ∘ σ)
        (fun i => t.presentation.weights_pos (σ i)) _ e he hp.1 hp.2.1 hp.2.2).trans
        (t.ternary_profile_pair_weight he σ hp.1 hp.2.1 hp.2.2).symm

end CanonicalRoots
