import CanonicalRoots.IsolatedAxisSupport

namespace CanonicalRoots

/-- I, II, III, IV, V, and the two branched patterns B1, B2. A loop denotes a pure power. -/
def threeAxisPattern (tag : Fin 7) : Fin 3 → Fin 3 :=
  ![![0,1,2], ![1,1,2], ![1,0,2], ![1,2,2], ![1,2,0], ![1,1,1], ![1,2,1]] tag

def threeCoordinatePermutation (r : Fin 6) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)] r

/-- All 27 axis-arrow maps, checked in the kernel, fall into the seven patterns. -/
theorem three_axis_map_seven_cases (f : Fin 3 → Fin 3) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 7, ∀ i, f (σ i) = σ (threeAxisPattern tag i) := by
  have h : ∀ f : Fin 3 → Fin 3, ∃ r : Fin 6, ∃ tag : Fin 7,
      ∀ i, f (threeCoordinatePermutation r i) = threeCoordinatePermutation r (threeAxisPattern tag i) := by
    decide +kernel
  obtain ⟨r, tag, hr⟩ := h f
  exact ⟨threeCoordinatePermutation r, tag, hr⟩

noncomputable section

/-- The seven-pattern reduction applies to an arbitrary actual isolated polynomial,
not only a polynomial already assumed to have three terms. -/
theorem isolated_ternary_seven_axis_patterns {h : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f)
    (w : Fin 3 → ℕ) (hhom : MvPolynomial.IsWeightedHomogeneous w f h)
    (hdef : (∑ i, w i) < h) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 7, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧ ∀ i,
        f.coeff (axisSupportExponent (σ i) (σ (threeAxisPattern tag i)) (k i)) ≠ 0 := by
  classical
  choose j k hk hc using isolated_positive_defect_axis_support f hf hlinear w hhom hdef
  obtain ⟨σ, tag, hσ⟩ := three_axis_map_seven_cases j
  refine ⟨σ, tag, k ∘ σ, fun i => hk (σ i), fun i => ?_⟩
  have hi := hc (σ i)
  rw [hσ i] at hi
  exact hi

end
end CanonicalRoots
