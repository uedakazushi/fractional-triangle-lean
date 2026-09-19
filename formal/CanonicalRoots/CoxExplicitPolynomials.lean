import CanonicalRoots.CoxCandidateRelation
import CanonicalRoots.BoundedMonomialBasis

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem monomial_three (d : Fin 3 →₀ ℕ) :
    monomial d (1 : ℂ) = X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2 := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_three]

/-- The executable exponent table gives exactly the five advertised equations. -/
theorem candidateRelation_explicit (kind : Cox.Kind) (α β γ : ℕ) :
    candidateRelation ⟨kind,α,β,γ⟩ =
      match kind with
      | .I => X 0 ^ α + X 1 ^ β + X 2 ^ γ
      | .II => X 0 ^ α * X 1 + X 1 ^ β + X 2 ^ γ
      | .III => X 0 ^ α * X 1 + X 0 * X 1 ^ β + X 2 ^ γ
      | .IV => X 0 ^ α * X 1 + X 1 ^ β * X 2 + X 2 ^ γ
      | .V => X 0 ^ α * X 1 + X 1 ^ β * X 2 + X 0 * X 2 ^ γ := by
  cases kind <;> simp [candidateRelation, Fin.sum_univ_three, monomial_three,
    candidateRelationExponent, Cox.exponents]

theorem candidateMonomial_explicit (kind : Cox.Kind) (α β γ : ℕ) (i : Fin 3) :
    candidateMonomial ⟨kind,α,β,γ⟩ i =
      (match kind with
      | .I => ![X 0, X 1, X 2]
      | .II => ![X 0, X 1 ^ γ, X 1 * X 2]
      | .III => ![X 0 ^ γ, X 1 ^ γ, X 0 * X 1 * X 2]
      | .IV => ![X 0 * X 2, X 1 ^ γ, X 1 * X 2 ^ α]
      | .V => ![X 0 ^ β * X 2, X 0 * X 1 ^ γ, X 1 * X 2 ^ α] :
        Fin 3 → MvPolynomial (Fin 3) ℂ) i := by
  cases kind <;> fin_cases i <;> simp [candidateMonomial, monomial_three,
    candidateMonomialExponent, Cox.monomials]

theorem oneArrow_relation_separated (α β γ : ℕ) :
    candidateRelation ⟨.II,α,β,γ⟩ =
      rename (Equiv.swap (0 : Fin 3) 2)
        (separatedRelation γ (X (1 : Fin 2) ^ α * X 0 + X 0 ^ β)) := by
  rw [candidateRelation_explicit]
  simp [separatedRelation, Equiv.swap_apply_def]
  ring

theorem twoCycle_relation_separated (α β γ : ℕ) :
    candidateRelation ⟨.III,α,β,γ⟩ =
      rename (Equiv.swap (0 : Fin 3) 2)
        (separatedRelation γ (X (1 : Fin 2) ^ α * X 0 + X 1 * X 0 ^ β)) := by
  rw [candidateRelation_explicit]
  simp [separatedRelation, Equiv.swap_apply_def]
  ring

end CanonicalRoots
