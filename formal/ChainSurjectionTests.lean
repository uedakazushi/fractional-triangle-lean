import CanonicalRoots.ChainSurjection

noncomputable section
open CanonicalRoots MvPolynomial

-- The root index and residue modulus are not coprime: cancellation by the index is invalid here.
example : ArithmeticTernary 2 ⟨.IV,3,4,2⟩ := by decide
example : candidateSignature ⟨.IV,3,4,2⟩ = ![3,7,3] := by decide
example (τ : DegreeGroup (candidateSignature ⟨.IV,3,4,2⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,3,4,2⟩) 2 τ) :
    Function.Surjective (candidateQuotientMap (by decide : 1 ≤ 2)
      (by decide : ArithmeticTernary 2 ⟨.IV,3,4,2⟩) τ hτ) :=
  candidateQuotientMap_surjective_chain (by decide) (by decide) τ hτ

-- The extra monomial cannot be written as a product of the three monomials before quotienting.
example (τ : DegreeGroup (candidateSignature ⟨.IV,3,4,2⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,3,4,2⟩) 2 τ) :
    (candidatePolynomialMap (by decide : 1 ≤ 2) (by decide : ArithmeticTernary 2 ⟨.IV,3,4,2⟩)
      τ hτ (-(X 0 ^ 3) - X 1 ^ 3 * X 2) : AmbientRing (candidateSignature ⟨.IV,3,4,2⟩)) =
      ambientQuotient (candidateSignature ⟨.IV,3,4,2⟩) (X 2 ^ 6) :=
  chain_extra_generator_image (by decide) (by decide) τ hτ

example : (∃ b c : ℕ, 7 = 2 * b + c ∧ 10 = 1 + 3 * c) ∨
    (∃ k : ℕ, 10 = 1 + 3 * 7 + (3 * 2) * k) :=
  chain_exponent_cases (by decide) (by decide) (by decide)
example : (∃ b c : ℕ, 1 = 2 * b + c ∧ 16 = 1 + 3 * c) ∨
    (∃ k : ℕ, 16 = 1 + 3 * 1 + (3 * 2) * k) :=
  chain_exponent_cases (by decide) (by decide) (by decide)
