import CanonicalRoots.LoopSurjection

noncomputable section
open CanonicalRoots MvPolynomial

example (τ : DegreeGroup (candidateSignature ⟨.V,2,3,5⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,2,3,5⟩) 7 τ) :
    Function.Surjective (candidateQuotientMap (by decide) (by decide) τ hτ) :=
  candidateQuotientMap_surjective_loop (by decide) (by decide) τ hτ

-- This corner exponent is not divisible by any of the three generators before reduction.
example (τ : DegreeGroup (candidateSignature ⟨.V,2,3,5⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,2,3,5⟩) 7 τ) :
    ∃ f : MvPolynomial (Fin 3) ℂ,
      (candidatePolynomialMap (by decide) (by decide) τ hτ f :
          AmbientRing (candidateSignature ⟨.V,2,3,5⟩)) =
        ambientQuotient _ (monomial (Finsupp.equivFunOnFinite.symm ![7,4,0]) 1) := by
  apply loop_polynomial_preimage (by decide) (by decide) τ hτ
  norm_num [LoopCongruence]

-- Pure-axis exponents require repeated use of the same generation induction.
example (τ : DegreeGroup (candidateSignature ⟨.V,2,3,5⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,2,3,5⟩) 7 τ) :
    ∃ f : MvPolynomial (Fin 3) ℂ,
      (candidatePolynomialMap (by decide) (by decide) τ hτ f :
          AmbientRing (candidateSignature ⟨.V,2,3,5⟩)) =
        ambientQuotient _ (monomial (Finsupp.single 0 31) 1) := by
  apply loop_polynomial_preimage (by decide) (by decide) τ hτ
  norm_num [LoopCongruence]
