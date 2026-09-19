import CanonicalRoots.ThreeAxisPatterns
import CanonicalRoots.TernaryPlaneArithmetic

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem three_branched_add_loop_reduces (tag : Fin 7) (ht : 5 ≤ tag.val)
    (i : Fin 3) (hi : i ≠ 1) :
    ∃ ρ : Equiv.Perm (Fin 3), ∃ t : Fin 5, ∀ l,
      (Function.update (threeAxisPattern tag) i i) (ρ l) =
        ρ (threeAxisPattern ⟨t.val, by omega⟩ l) := by
  have h : ∀ tag : Fin 7, 5 ≤ tag.val → ∀ i : Fin 3, i ≠ 1 →
      ∃ r : Fin 6, ∃ t : Fin 5, ∀ l,
        (Function.update (threeAxisPattern tag) i i) (threeCoordinatePermutation r l) =
          threeCoordinatePermutation r (threeAxisPattern ⟨t.val, Nat.lt_trans t.isLt (by decide : 5 < 7)⟩ l) := by
    decide +kernel
  obtain ⟨r, t, hrt⟩ := h tag ht i hi
  exact ⟨threeCoordinatePermutation r, t, hrt⟩

theorem branched_axis_support_add_pure (f : MvPolynomial (Fin 3) ℂ)
    (σ : Equiv.Perm (Fin 3)) (tag : Fin 7) (ht : 5 ≤ tag.val)
    (k : Fin 3 → ℕ) (hk : ∀ i, 2 ≤ k i)
    (hc : ∀ i, f.coeff (axisSupportExponent (σ i) (σ (threeAxisPattern tag i)) (k i)) ≠ 0)
    (i : Fin 3) (hi : i ≠ 1) (m : ℕ) (hm : 2 ≤ m)
    (hpure : f.coeff (Finsupp.single (σ i) m) ≠ 0) :
    ∃ σ' : Equiv.Perm (Fin 3), ∃ t : Fin 5, ∃ k' : Fin 3 → ℕ,
      (∀ l, 2 ≤ k' l) ∧ ∀ l,
        f.coeff (axisSupportExponent (σ' l) (σ' (threeAxisPattern ⟨t.val, by omega⟩ l))
          (k' l)) ≠ 0 := by
  classical
  obtain ⟨ρ, t, hρ⟩ := three_branched_add_loop_reduces tag ht i hi
  refine ⟨ρ.trans σ, t, (Function.update k i m) ∘ ρ, ?_, ?_⟩
  · intro l
    by_cases hl : ρ l = i
    · simpa [hl] using hm
    · simpa [hl] using hk (ρ l)
  · intro l
    change f.coeff (axisSupportExponent (σ (ρ l))
      (σ (ρ (threeAxisPattern ⟨t.val, by omega⟩ l))) (Function.update k i m (ρ l))) ≠ 0
    rw [← hρ l]
    by_cases hl : ρ l = i
    · simpa [hl, axisSupportExponent] using hpure
    · simpa [hl] using hc (ρ l)

theorem pure_coefficient_exponent_ge_two {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : HasNoConstantOrLinear f) (i : Fin n) (m : ℕ)
    (hm : f.coeff (Finsupp.single i m) ≠ 0) : 2 ≤ m := by
  by_contra hn
  have he : m = 0 ∨ m = 1 := by omega
  rcases he with rfl | rfl
  · simpa [hf.1] using hm
  · exact hm (hf.2 i)

/-- Either an invertible three-term support occurs, or a branched support has an
actual positive link. The polynomial is still arbitrary and may have other terms. -/
theorem isolated_ternary_five_or_branched_link {h : ℕ}
    (f : MvPolynomial (Fin 3) ℂ) (hf : IsolatedAtOrigin f)
    (hlinear : HasNoConstantOrLinear f) (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (hhom : IsWeightedHomogeneous w f h) (hdef : (∑ i, w i) < h) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 7, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧
      (∀ i, f.coeff (axisSupportExponent (σ i) (σ (threeAxisPattern tag i)) (k i)) ≠ 0) ∧
      (tag.val < 5 ∨ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        f.coeff (Finsupp.single (σ 0) m + Finsupp.single (σ 2) n) ≠ 0) := by
  classical
  obtain ⟨σ, tag, k, hk, hc⟩ := isolated_ternary_seven_axis_patterns f hf hlinear w hhom hdef
  by_cases ht : tag.val < 5
  · exact ⟨σ, tag, k, hk, hc, Or.inl ht⟩
  have htag : 5 ≤ tag.val := by omega
  obtain ⟨d, hd1, hd⟩ := isolated_ternary_plane_coefficient f hf hlinear w hw hhom (σ 1)
  have heq : d = Finsupp.single (σ 0) (d (σ 0)) + Finsupp.single (σ 2) (d (σ 2)) := by
    ext j
    obtain ⟨i, rfl⟩ := σ.surjective j
    fin_cases i <;> simp [σ.injective.eq_iff, hd1]
  have hfinish : ∀ (i : Fin 3) (m : ℕ), i ≠ 1 → 2 ≤ m →
      f.coeff (Finsupp.single (σ i) m) ≠ 0 →
      ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 7, ∃ k : Fin 3 → ℕ,
        (∀ i, 2 ≤ k i) ∧
        (∀ i, f.coeff (axisSupportExponent (σ i) (σ (threeAxisPattern tag i)) (k i)) ≠ 0) ∧
        (tag.val < 5 ∨ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
          f.coeff (Finsupp.single (σ 0) m + Finsupp.single (σ 2) n) ≠ 0) := by
    intro i m hi hm hcoeff
    obtain ⟨σ', t, k', hk', hc'⟩ := branched_axis_support_add_pure f σ tag htag k hk hc i hi m hm hcoeff
    exact ⟨σ', ⟨t.val, by omega⟩, k', hk', hc', Or.inl t.isLt⟩
  by_cases h0 : d (σ 0) = 0
  · have hpure : f.coeff (Finsupp.single (σ 2) (d (σ 2))) ≠ 0 := by
      have hx := hd
      rw [heq] at hx
      simpa only [h0, Finsupp.single_zero, zero_add] using hx
    exact hfinish 2 _ (by decide) (pure_coefficient_exponent_ge_two f hlinear _ _ hpure) hpure
  by_cases h2 : d (σ 2) = 0
  · have hpure : f.coeff (Finsupp.single (σ 0) (d (σ 0))) ≠ 0 := by
      have hx := hd
      rw [heq] at hx
      simpa only [h2, Finsupp.single_zero, add_zero] using hx
    exact hfinish 0 _ (by decide) (pure_coefficient_exponent_ge_two f hlinear _ _ hpure) hpure
  exact ⟨σ, tag, k, hk, hc, Or.inr ⟨d (σ 0), d (σ 2), Nat.pos_of_ne_zero h0,
    Nat.pos_of_ne_zero h2, heq ▸ hd⟩⟩

end CanonicalRoots
