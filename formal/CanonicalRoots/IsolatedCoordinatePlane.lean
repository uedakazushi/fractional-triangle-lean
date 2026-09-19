import CanonicalRoots.TernaryLineSlice

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem homogeneous_of_X_mul {n h : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (j : Fin n) (hf : IsWeightedHomogeneous w (X j * g) h) :
    IsWeightedHomogeneous w g (h - w j) := by
  intro d hd
  have hc : (X j * g).coeff (Finsupp.single j 1 + d) ≠ 0 := by simpa using hd
  have hh := hf hc
  simp only [map_add, Finsupp.weight_single, one_smul] at hh
  omega

theorem eval_pderiv_X_mul_eq_zero {n : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (j : Fin n) (z : Fin n → ℂ) (hz : z j = 0) (hg : eval z g = 0) (i : Fin n) :
    eval z (pderiv i (X j * g)) = 0 := by
  simp [pderiv_mul, hz, hg]

/-- An isolated ternary polynomial cannot vanish identically on a coordinate plane.
This elementary proof uses a univariate complex root, without a normality hypothesis. -/
theorem isolated_ternary_not_X_one_dvd {h : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f)
    (w : Fin 3 → ℕ) (hw : 0 < w 2) (hhom : IsWeightedHomogeneous w f h) :
    ¬ X 1 ∣ f := by
  rintro ⟨g, rfl⟩
  have hg : IsWeightedHomogeneous w g (h - w 1) := homogeneous_of_X_mul g w 1 hhom
  have hg0 : g.coeff 0 = 0 := by
    rw [← coeff_X_mul 0 1 g]
    simpa using hlinear.2 1
  have hx : eval (Pi.single 0 1) g ≠ 0 := by
    intro he
    have hz := (hf (Pi.single 0 1)).mp
      (eval_pderiv_X_mul_eq_zero g 1 (Pi.single 0 1) (by simp) he)
    have := congrFun hz 0
    simp at this
  obtain ⟨x, hx⟩ := weighted_ternary_has_nonzero_plane_zero g w hw hg hx hg0
  have hz := (hf ![x,0,1]).mp
    (eval_pderiv_X_mul_eq_zero g 1 ![x,0,1] (by simp) hx)
  have := congrFun hz 2
  simp at this

end CanonicalRoots
