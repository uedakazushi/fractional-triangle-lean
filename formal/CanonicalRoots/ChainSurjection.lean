import CanonicalRoots.ChainExtraGenerator
import CanonicalRoots.ChainRootExponents
import CanonicalRoots.PermutedRootMonomials

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- The chain lattice congruence supplies an actual polynomial preimage. -/
theorem chain_polynomial_preimage {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ)
    (d : Fin 3 →₀ ℕ) (hd0 : d 0 < α)
    (hd : ∃ m : ℕ, Finsupp.weight (xDegree (candidateSignature ⟨.IV,α,β,γ⟩)) d = m • τ) :
    ∃ f : MvPolynomial (Fin 3) ℂ,
      (candidatePolynomialMap ha he τ hτ f : AmbientRing (candidateSignature ⟨.IV,α,β,γ⟩)) =
        ambientQuotient (candidateSignature ⟨.IV,α,β,γ⟩) (monomial d 1) := by
  have hα : 0 < α := by have hh : 2 ≤ α := he.1; omega
  have hdiv := chain_root_monomial_divisibility ha he τ hτ d hd
  rcases chain_exponent_cases hα hd0 hdiv with ⟨b,c,h1,h2⟩ | ⟨k,h2⟩
  · refine ⟨X 0 ^ d 0 * X 1 ^ b * X 2 ^ c, ?_⟩
    change ((rootSubalgebra _ τ).val.comp (candidatePolynomialMap ha he τ hτ)) _ = _
    rw [candidatePolynomialMap_val]
    change ambientQuotient _ (aeval (candidateMonomial ⟨.IV,α,β,γ⟩) _) = _
    apply congrArg (ambientQuotient _)
    simp only [map_mul, map_pow, aeval_X, candidateMonomial_explicit]
    dsimp
    rw [monomial_three, h1, h2]
    simp only [mul_pow, pow_mul, pow_add]
    ring
  · refine ⟨X 0 ^ d 0 * X 2 ^ d 1 * (-(X 0 ^ α) - X 1 ^ (β - 1) * X 2) ^ k, ?_⟩
    change ((rootSubalgebra _ τ).val.comp (candidatePolynomialMap ha he τ hτ)) _ = _
    simp only [map_mul, map_pow]
    have hQ := chain_extra_generator_image ha he τ hτ
    change ((rootSubalgebra _ τ).val.comp (candidatePolynomialMap ha he τ hτ)) _ = _ at hQ
    rw [hQ, candidatePolynomialMap_val]
    simp only [AlgHom.comp_apply, aeval_X]
    change ambientQuotient _ (candidateMonomial ⟨.IV,α,β,γ⟩ 0) ^ d 0 *
      ambientQuotient _ (candidateMonomial ⟨.IV,α,β,γ⟩ 2) ^ d 1 *
      ambientQuotient _ (X 2 ^ (α * γ)) ^ k = _
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    apply congrArg (ambientQuotient _)
    rw [monomial_three, h2]
    simp only [candidateMonomial_explicit]
    dsimp
    simp only [mul_pow, pow_mul, pow_add]
    ring

/-- Type IV Cox generators generate the entire actual canonical-root ring. -/
theorem candidateQuotientMap_surjective_chain {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) :
    Function.Surjective (candidateQuotientMap ha he τ hτ) := by
  apply rootMap_surjective_of_permuted_monomials (candidateSignature ⟨.IV,α,β,γ⟩)
    (Equiv.refl _) (by have := candidateSignature_ge_two he 0; simpa using (show 0 < candidateSignature ⟨.IV,α,β,γ⟩ 0 by omega)) τ
  intro d hd0 hd
  have hb : d 0 < α := by simpa [chain_signature_nat he] using hd0
  obtain ⟨f,hf⟩ := chain_polynomial_preimage ha he τ hτ d hb hd
  refine ⟨(Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.IV,α,β,γ⟩})) f, ?_⟩
  rw [candidateQuotientMap_mk]
  exact hf

end CanonicalRoots
