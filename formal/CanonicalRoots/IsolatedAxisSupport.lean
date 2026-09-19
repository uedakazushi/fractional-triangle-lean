import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem exists_pure_coefficient_of_axis_eval_ne_zero {n : ℕ}
    (f : MvPolynomial (Fin n) ℂ) (i : Fin n) (h : eval (Pi.single i 1) f ≠ 0) :
    ∃ k : ℕ, f.coeff (Finsupp.single i k) ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply h
  apply eval₂Hom_eq_zero
  intro d hd
  have hdiff : ∃ j, j ≠ i ∧ d j ≠ 0 := by
    by_contra he
    push Not at he
    have heq : d = Finsupp.single i (d i) := by
      ext j
      by_cases hji : j = i
      · subst j; simp
      · simp [hji, he j hji]
    exact hd (by rw [heq]; exact hn (d i))
  obtain ⟨j, hji, hdj⟩ := hdiff
  exact ⟨j, Finsupp.mem_support_iff.mpr hdj, by simp [hji]⟩

/-- Isolatedness forces an actual nonzero pure-power or one-arrow coefficient
at each coordinate axis. -/
theorem isolated_axis_coefficient {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f) (i : Fin n) :
    ∃ j : Fin n, ∃ k : ℕ, 1 ≤ k ∧
      f.coeff (Finsupp.single i k + Finsupp.single j 1) ≠ 0 := by
  classical
  have hx : (Pi.single i (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
    intro he
    have := congrFun he i
    simp at this
  have hd : ∃ j, eval (Pi.single i 1) (pderiv j f) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx ((hf _).mp hn)
  obtain ⟨j, hj⟩ := hd
  obtain ⟨k, hk⟩ := exists_pure_coefficient_of_axis_eval_ne_zero (pderiv j f) i hj
  rw [coeff_pderiv] at hk
  have hc : f.coeff (Finsupp.single i k + Finsupp.single j 1) ≠ 0 :=
    left_ne_zero_of_mul hk
  refine ⟨j, k, ?_, hc⟩
  by_contra hpos
  have hk0 : k = 0 := by omega
  subst k
  simp [hlinear.2 j] at hc

def axisSupportExponent {n : ℕ} (i j : Fin n) (k : ℕ) : Fin n →₀ ℕ :=
  if i = j then Finsupp.single i k else Finsupp.single i k + Finsupp.single j 1

/-- A positive defect rules out mixed quadratic terms, so every axis has a
pure power or an arrow term whose main exponent is at least two. -/
theorem isolated_positive_defect_axis_support {n h : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f)
    (w : Fin n → ℕ) (hhom : IsWeightedHomogeneous w f h) (hdef : (∑ i, w i) < h)
    (i : Fin n) : ∃ j : Fin n, ∃ k : ℕ, 2 ≤ k ∧ f.coeff (axisSupportExponent i j k) ≠ 0 := by
  classical
  obtain ⟨j, k, hk, hc⟩ := isolated_axis_coefficient f hf hlinear i
  by_cases hij : i = j
  · subst j
    refine ⟨i, k + 1, by omega, ?_⟩
    simpa [axisSupportExponent, ← Finsupp.single_add] using hc
  · refine ⟨j, k, ?_, by simpa only [axisSupportExponent, ite_eq_right hij] using hc⟩
    by_contra hlt
    have hk1 : k = 1 := by omega
    subst k
    have he := hhom hc
    simp only [map_add, Finsupp.weight_single, one_smul] at he
    have hsum : w i + w j ≤ ∑ l, w l := by
      calc
        _ = ∑ l ∈ ({i,j} : Finset (Fin n)), w l := (Finset.sum_pair hij).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

end CanonicalRoots
