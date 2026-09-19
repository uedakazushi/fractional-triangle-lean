import CanonicalRoots.IsolatedAxisSupport

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- The polynomial on the affine chart `(x,0,1)` of the coordinate plane. -/
def ternaryLineSlice (f : MvPolynomial (Fin 3) ℂ) : Polynomial ℂ :=
  ∑ d ∈ f.support, if d 1 = 0 then Polynomial.monomial (d 0) (f.coeff d) else 0

theorem ternaryLineSlice_eval (f : MvPolynomial (Fin 3) ℂ) (x : ℂ) :
    (ternaryLineSlice f).eval x = eval ![x,0,1] f := by
  classical
  change _ = f.eval₂ (RingHom.id _) ![x,0,1]
  rw [eval₂_eq']
  simp only [ternaryLineSlice, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d 1 = 0
  · simp [h, Fin.prod_univ_succ]
  · simp [h, Fin.prod_univ_succ]

/-- Homogeneity prevents cancellation of a pure-axis coefficient in this chart. -/
theorem ternaryLineSlice_coeff {h r : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (w : Fin 3 → ℕ) (hw : 0 < w 2) (hf : IsWeightedHomogeneous w f h)
    (hr : r * w 0 = h) :
    (ternaryLineSlice f).coeff r = f.coeff (Finsupp.single 0 r) := by
  classical
  simp only [ternaryLineSlice, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (Finsupp.single 0 r)]
  · simp
  · intro d hd hne
    have hd' := hf (mem_support_iff.mp hd)
    by_cases h1 : d 1 = 0
    · by_cases h0 : d 0 = r
      · have h2 : d 2 = 0 := by
          simp only [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul,
            h0, h1, zero_mul, add_zero] at hd'
          nlinarith
        have he : d = Finsupp.single 0 r := by
          ext i
          fin_cases i <;> simp_all
        exact False.elim (hne he)
      · simp [h1, Polynomial.coeff_monomial, h0]
    · simp [h1]
  · intro hn
    simp [notMem_support_iff.mp hn]

theorem weighted_ternary_has_nonzero_plane_zero {h : ℕ}
    (f : MvPolynomial (Fin 3) ℂ) (w : Fin 3 → ℕ) (hw : 0 < w 2)
    (hf : IsWeightedHomogeneous w f h)
    (hx : eval (Pi.single 0 1) f ≠ 0) (hconst : f.coeff 0 = 0) :
    ∃ x : ℂ, eval ![x,0,1] f = 0 := by
  obtain ⟨r, hr⟩ := exists_pure_coefficient_of_axis_eval_ne_zero f 0 hx
  have hr0 : r ≠ 0 := by rintro rfl; simpa [hconst] using hr
  have hweight : r * w 0 = h := by
    simpa only [Finsupp.weight_single, smul_eq_mul] using hf hr
  have hc := ternaryLineSlice_coeff f w hw hf hweight
  have hdeg : (ternaryLineSlice f).degree ≠ 0 := by
    intro he
    have hC := Polynomial.eq_C_of_degree_eq_zero he
    have := congrArg (fun p : Polynomial ℂ => p.coeff r) hC
    simp [hc, Polynomial.coeff_C, hr0, Ne.symm hr0] at this
    exact hr this
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (ternaryLineSlice f) hdeg
  exact ⟨x, by simpa only [Polynomial.IsRoot, ternaryLineSlice_eval] using hx⟩

end CanonicalRoots
