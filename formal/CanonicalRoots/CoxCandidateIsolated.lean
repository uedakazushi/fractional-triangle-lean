import CanonicalRoots.CoxGradientTerms

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Each actual Cox candidate equation has the origin as its only critical point. -/
theorem candidateRelation_isolated {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : IsolatedAtOrigin (candidateRelation e) := by
  intro z
  rcases e with ⟨kind,α,β,γ⟩
  have hα : 2 ≤ α := he.1
  have hβ : 2 ≤ β := he.2.1
  have hγ : 2 ≤ γ := he.2.2.1
  have ha : α ≠ 0 := by omega
  have hb : β ≠ 0 := by omega
  have hc : γ ≠ 0 := by omega
  have ha1 : α - 1 ≠ 0 := by omega
  have hb1 : β - 1 ≠ 0 := by omega
  have hc1 : γ - 1 ≠ 0 := by omega
  constructor
  · intro hz
    have h0 := candidate_gradient_terms_zero he z hz 0
    have h1 := candidate_gradient_terms_zero he z hz 1
    have h2 := candidate_gradient_terms_zero he z hz 2
    have hd0 := hz 0
    have hd1 := hz 1
    have hd2 := hz 2
    cases kind
    · simp [candidateRelationExponent, Cox.exponents, monomial_three, ha, hb, hc] at h0 h1 h2
      have hx : z 0 = 0 := h0
      have hy : z 1 = 0 := h1
      have hz : z 2 = 0 := h2
      ext i
      fin_cases i <;> simp [hx,hy,hz]
    · simp [candidateRelationExponent, Cox.exponents, monomial_three, ha, hb, hc] at h1 h2
      have hy : z 1 = 0 := h1
      have hz : z 2 = 0 := h2
      have hx : z 0 = 0 := by
        simpa [candidateRelation_explicit, pderiv_mul, hy, hb1, pow_eq_zero_iff ha] using hd1
      ext i
      fin_cases i <;> simp [hx,hy,hz]
    · simp [candidateRelationExponent, Cox.exponents, monomial_three, ha, hb, hc] at h0 h2
      have hz : z 2 = 0 := h2
      have hxy : z 0 = 0 ∨ z 1 = 0 := by simpa [pow_eq_zero_iff ha] using h0
      have hx : z 0 = 0 := by
        rcases hxy with hx | hy
        · exact hx
        · simpa [candidateRelation_explicit, pderiv_mul, hy, hb1, pow_eq_zero_iff ha] using hd1
      have hy : z 1 = 0 := by
        simpa [candidateRelation_explicit, pderiv_mul, hx, ha1, pow_eq_zero_iff hb] using hd0
      ext i
      fin_cases i <;> simp [hx,hy,hz]
    · simp [candidateRelationExponent, Cox.exponents, monomial_three, ha, hb, hc] at h2
      have hz : z 2 = 0 := h2
      have hy : z 1 = 0 := by
        simpa [candidateRelation_explicit, pderiv_mul, hz, hc1, pow_eq_zero_iff hb] using hd2
      have hx : z 0 = 0 := by
        simpa [candidateRelation_explicit, pderiv_mul, hz, pow_eq_zero_iff ha] using hd1
      ext i
      fin_cases i <;> simp [hx,hy,hz]
    · simp [candidateRelationExponent, Cox.exponents, monomial_three, ha, hb, hc] at h0
      have hxy : z 0 = 0 ∨ z 1 = 0 := by simpa [pow_eq_zero_iff ha] using h0
      have hx : z 0 = 0 := by
        rcases hxy with hx | hy
        · exact hx
        · simpa [candidateRelation_explicit, pderiv_mul, hy, hb1, pow_eq_zero_iff ha] using hd1
      have hz : z 2 = 0 := by
        simpa [candidateRelation_explicit, pderiv_mul, hx, ha1, pow_eq_zero_iff hc] using hd0
      have hy : z 1 = 0 := by
        simpa [candidateRelation_explicit, pderiv_mul, hx, pow_eq_zero_iff hb] using hd2
      ext i
      fin_cases i <;> simp [hx,hy,hz]
  · rintro rfl i
    cases kind <;> fin_cases i <;>
      simp [candidateRelation_explicit, pderiv_mul, ha, hb, hc, ha1, hb1, hc1]

end CanonicalRoots
