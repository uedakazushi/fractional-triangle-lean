import CanonicalRoots.MonicQuotientBasis
import CanonicalRoots.CoxExplicitPolynomials

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def chainReverseRelation (α β γ : ℕ) : MvPolynomial (Fin 3) ℂ :=
  X 0 ^ γ + (X 1 ^ β * X 0 + X 2 ^ α * X 1)

theorem chain_relation_reversed (α β γ : ℕ) :
    candidateRelation ⟨.IV,α,β,γ⟩ = rename (Equiv.swap (0 : Fin 3) 2) (chainReverseRelation α β γ) := by
  simp [candidateRelation_explicit, chainReverseRelation, Equiv.swap_apply_def]
  ring

theorem finSuccEquiv_chainReverseRelation (α β γ : ℕ) :
    finSuccEquiv ℂ 2 (chainReverseRelation α β γ) = Polynomial.X ^ γ +
      (Polynomial.C (X (0 : Fin 2) ^ β) * Polynomial.X + Polynomial.C (X 1 ^ α * X 0)) := by
  have h1 : finSuccEquiv ℂ 2 (X 1) = Polynomial.C (X (0 : Fin 2)) :=
    finSuccEquiv_X_succ (R := ℂ) (n := 2) (j := 0)
  have h2 : finSuccEquiv ℂ 2 (X 2) = Polynomial.C (X (1 : Fin 2)) :=
    finSuccEquiv_X_succ (R := ℂ) (n := 2) (j := 1)
  simp [chainReverseRelation, finSuccEquiv_X_zero, h1, h2]

theorem chainReverseRelation_monic (α β γ : ℕ) (hγ : 2 ≤ γ) :
    (finSuccEquiv ℂ 2 (chainReverseRelation α β γ)).Monic := by
  rw [finSuccEquiv_chainReverseRelation]
  apply Polynomial.monic_X_pow_add
  exact lt_of_lt_of_le Polynomial.degree_linear_lt (by exact_mod_cast hγ)

theorem chainReverseRelation_natDegree (α β γ : ℕ) (hγ : 2 ≤ γ) :
    (finSuccEquiv ℂ 2 (chainReverseRelation α β γ)).natDegree = γ := by
  rw [finSuccEquiv_chainReverseRelation]
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_add_eq_left_of_degree_lt]
  · simp
  · rw [Polynomial.degree_X_pow]
    exact lt_of_lt_of_le Polynomial.degree_linear_lt (by exact_mod_cast hγ)

theorem candidateChainMonomials_span (α β γ : ℕ) (hγ : 2 ≤ γ) :
    Submodule.span ℂ (Set.range (fun d : {d : Fin 3 →₀ ℕ // d 2 < γ} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.IV,α,β,γ⟩})) (monomial d.val 1))) = ⊤ := by
  rw [chain_relation_reversed]
  have hh := monicQuotientPermutedMonomials_span (chainReverseRelation α β γ)
    (chainReverseRelation_monic α β γ hγ) (Equiv.swap (0 : Fin 3) 2)
  rw [chainReverseRelation_natDegree α β γ hγ] at hh
  convert hh using 1 <;> norm_num [Equiv.swap_apply_def]
  congr 1

end CanonicalRoots
