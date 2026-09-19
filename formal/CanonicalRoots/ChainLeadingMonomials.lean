import CanonicalRoots.ChainExtraGenerator
import CanonicalRoots.LeadingMonomialIndependence

noncomputable section
namespace CanonicalRoots
open MvPolynomial
open scoped MonomialOrder

/-- Reversed ambient coordinates put the reducing Z term first in the lexicographic order. -/
def chainReductionTail (α β γ : ℕ) : MvPolynomial (Fin 3) ℂ :=
  -(X 1 ^ (γ * (β - 1) + 1) + X 0 ^ (α * (γ - 1)))

def chainReducedMonomial (α β γ : ℕ) (d : Fin 3 →₀ ℕ) : MvPolynomial (Fin 3) ℂ :=
  X 2 ^ (d 0 % α) * X 1 ^ (γ * d 1 + d 2) * X 0 ^ (d 0 + α * d 2) *
    chainReductionTail α β γ ^ (d 0 / α)

def chainLeadingExponent (α γ : ℕ) (d : Fin 3 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![d 0 + α * d 2 + α * (γ - 1) * (d 0 / α), γ * d 1 + d 2, d 0 % α]

theorem chainReductionTail_degree {α β γ : ℕ} (hα : 0 < α) (hγ : 2 ≤ γ) :
    MonomialOrder.lex.degree (chainReductionTail α β γ) =
      (α * (γ - 1)) • Finsupp.single (0 : Fin 3) 1 := by
  have hp : 0 < α * (γ - 1) := Nat.mul_pos hα (by omega)
  have hlt : MonomialOrder.lex.degree (X (1 : Fin 3) ^ (γ * (β - 1) + 1) : MvPolynomial (Fin 3) ℂ)
      ≺[MonomialOrder.lex] MonomialOrder.lex.degree (X (0 : Fin 3) ^ (α * (γ - 1)) : MvPolynomial (Fin 3) ℂ) := by
    simp only [MonomialOrder.degree_pow, MonomialOrder.degree_X]
    rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
    refine ⟨0, ?_, ?_⟩
    · intro j hj
      exact (Fin.not_lt_zero j hj).elim
    · simpa using hp
  rw [chainReductionTail, MonomialOrder.degree_neg,
    MonomialOrder.degree_add_eq_right_of_lt hlt, MonomialOrder.degree_pow, MonomialOrder.degree_X]

theorem chainReductionTail_ne_zero {α β γ : ℕ} (hα : 0 < α) (hγ : 2 ≤ γ) :
    chainReductionTail α β γ ≠ 0 := by
  apply MonomialOrder.lex.ne_zero_of_degree_ne_zero
  rw [chainReductionTail_degree hα hγ]
  intro hh
  have hh0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) hh
  have hp : 0 < α * (γ - 1) := Nat.mul_pos hα (by omega)
  simp at hh0
  omega

theorem chainReducedMonomial_ne_zero {α β γ : ℕ} (hα : 0 < α) (hγ : 2 ≤ γ)
    (d : Fin 3 →₀ ℕ) : chainReducedMonomial α β γ d ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_ne_zero 2))
      (pow_ne_zero _ (X_ne_zero 1))) (pow_ne_zero _ (X_ne_zero 0))
  · exact pow_ne_zero _ (chainReductionTail_ne_zero hα hγ)

theorem chainReducedMonomial_degree {α β γ : ℕ} (hα : 0 < α) (hγ : 2 ≤ γ)
    (d : Fin 3 →₀ ℕ) :
    MonomialOrder.lex.degree (chainReducedMonomial α β γ d) = chainLeadingExponent α γ d := by
  have hn0 (n : ℕ) (i : Fin 3) : (X i ^ n : MvPolynomial (Fin 3) ℂ) ≠ 0 :=
    pow_ne_zero _ (X_ne_zero _)
  have hnt := pow_ne_zero (d 0 / α) (chainReductionTail_ne_zero (β := β) hα hγ)
  rw [chainReducedMonomial,
    MonomialOrder.degree_mul (mul_ne_zero (mul_ne_zero (hn0 _ _) (hn0 _ _)) (hn0 _ _)) hnt,
    MonomialOrder.degree_mul (mul_ne_zero (hn0 _ _) (hn0 _ _)) (hn0 _ _),
    MonomialOrder.degree_mul (hn0 _ _) (hn0 _ _)]
  simp only [MonomialOrder.degree_pow, MonomialOrder.degree_X, chainReductionTail_degree hα hγ]
  ext i
  fin_cases i <;> simp [chainLeadingExponent, Nat.mul_comm]

theorem chainLeadingExponent_injective {α γ : ℕ} (hα : 0 < α) (hγ : 0 < γ) :
    Function.Injective (fun d : {d : Fin 3 →₀ ℕ // d 2 < γ} => chainLeadingExponent α γ d.val) := by
  intro d b hh
  have h0 := congrArg (fun v : Fin 3 →₀ ℕ => v 0) hh
  have h1 := congrArg (fun v : Fin 3 →₀ ℕ => v 1) hh
  have h2 := congrArg (fun v : Fin 3 →₀ ℕ => v 2) hh
  simp [chainLeadingExponent] at h0 h1 h2
  have hremd := Nat.mod_add_div (d.val 0) α
  have hremb := Nat.mod_add_div (b.val 0) α
  have he : γ * (d.val 0 / α) + d.val 2 = γ * (b.val 0 / α) + b.val 2 := by
    have hg : γ - 1 + 1 = γ := Nat.sub_add_cancel hγ
    nlinarith
  have hc : d.val 2 = b.val 2 := by
    have hr := congrArg (fun n => n % γ) he
    simpa [Nat.add_mod, Nat.mod_eq_of_lt d.property, Nat.mod_eq_of_lt b.property] using hr
  have hq : d.val 0 / α = b.val 0 / α := by nlinarith
  apply Subtype.ext
  ext i
  fin_cases i
  · change d.val 0 = b.val 0
    calc
      _ = d.val 0 % α + α * (d.val 0 / α) := hremd.symm
      _ = b.val 0 % α + α * (b.val 0 / α) := by rw [h2,hq]
      _ = b.val 0 := hremb
  · change d.val 1 = b.val 1
    nlinarith
  · exact hc

theorem chainReducedMonomials_linearIndependent {α β γ : ℕ} (hα : 0 < α) (hγ : 2 ≤ γ) :
    LinearIndependent ℂ (fun d : {d : Fin 3 →₀ ℕ // d 2 < γ} => chainReducedMonomial α β γ d.val) := by
  apply linearIndependent_of_distinct_leading_monomials MonomialOrder.lex
  · exact fun d => chainReducedMonomial_ne_zero hα hγ d.val
  · simpa only [chainReducedMonomial_degree hα hγ] using
      chainLeadingExponent_injective hα (by omega : 0 < γ)

end CanonicalRoots
