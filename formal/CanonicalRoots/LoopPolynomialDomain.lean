import CanonicalRoots.MonicQuotientBasis
import CanonicalRoots.CoxExplicitPolynomials
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def loopReverseRelation (α β γ : ℕ) : MvPolynomial (Fin 3) ℂ :=
  X 2 * X 0 ^ γ + (X 1 ^ β * X 0 + X 2 ^ α * X 1)

def loopSplitPolynomial (α β γ : ℕ) : Polynomial (MvPolynomial (Fin 2) ℂ) :=
  Polynomial.C (X 1) * Polynomial.X ^ γ +
    (Polynomial.C (X 0 ^ β) * Polynomial.X + Polynomial.C (X 1 ^ α * X 0))

theorem loop_relation_reversed (α β γ : ℕ) :
    candidateRelation ⟨.V,α,β,γ⟩ = rename (Equiv.swap (0 : Fin 3) 2) (loopReverseRelation α β γ) := by
  simp [candidateRelation_explicit, loopReverseRelation, Equiv.swap_apply_def]
  ring

theorem finSuccEquiv_loopReverseRelation (α β γ : ℕ) :
    finSuccEquiv ℂ 2 (loopReverseRelation α β γ) = loopSplitPolynomial α β γ := by
  have h1 : finSuccEquiv ℂ 2 (X 1) = Polynomial.C (X (0 : Fin 2)) :=
    finSuccEquiv_X_succ (R := ℂ) (n := 2) (j := 0)
  have h2 : finSuccEquiv ℂ 2 (X 2) = Polynomial.C (X (1 : Fin 2)) :=
    finSuccEquiv_X_succ (R := ℂ) (n := 2) (j := 1)
  simp [loopReverseRelation, loopSplitPolynomial, finSuccEquiv_X_zero, h1, h2]

theorem mv_X_not_dvd_other_pow {σ : Type*} [DecidableEq σ] (i j : σ) (hij : i ≠ j) (k : ℕ) :
    ¬ (X i : MvPolynomial σ ℂ) ∣ X j ^ k := by
  intro h
  have hh := map_dvd (eval (fun l => if l = i then (0 : ℂ) else 1)) h
  simpa [hij, hij.symm] using hh

theorem loopSplitPolynomial_degree (α β γ : ℕ) (hγ : 2 ≤ γ) :
    (loopSplitPolynomial α β γ).degree = γ := by
  unfold loopSplitPolynomial
  rw [Polynomial.degree_add_eq_left_of_degree_lt]
  · exact Polynomial.degree_C_mul_X_pow γ (X_ne_zero 1)
  · rw [Polynomial.degree_C_mul_X_pow γ (X_ne_zero 1)]
    exact lt_of_lt_of_le Polynomial.degree_linear_lt (by exact_mod_cast hγ)

theorem loopSplitPolynomial_leadingCoeff (α β γ : ℕ) (hγ : 2 ≤ γ) :
    (loopSplitPolynomial α β γ).leadingCoeff = X 1 := by
  unfold loopSplitPolynomial
  rw [Polynomial.leadingCoeff_add_of_degree_lt']
  · exact Polynomial.leadingCoeff_C_mul_X_pow _ _
  · rw [Polynomial.degree_C_mul_X_pow γ (X_ne_zero 1)]
    exact lt_of_lt_of_le Polynomial.degree_linear_lt (by exact_mod_cast hγ)

theorem loopSplitPolynomial_coeff (α β γ n : ℕ) :
    (loopSplitPolynomial α β γ).coeff n =
      (if γ = n then X 1 else 0) +
        ((if 1 = n then X 0 ^ β else 0) + (if n = 0 then X 1 ^ α * X 0 else 0)) := by
  simp only [loopSplitPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  simp [eq_comm]

/-- Eisenstein at the second variable proves the loop equation irreducible. -/
theorem loopSplitPolynomial_irreducible (α β γ : ℕ) (hβ : 1 ≤ β) (hγ : 2 ≤ γ) :
    Irreducible (loopSplitPolynomial α β γ) := by
  let P : Ideal (MvPolynomial (Fin 2) ℂ) := Ideal.span {X 0}
  have hx : Prime (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) := MvPolynomial.X_prime
  have hy : Prime (X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) := MvPolynomial.X_prime
  have hγ0 : γ ≠ 0 := by omega
  have hγ1 : γ ≠ 1 := by omega
  have hc0 : (loopSplitPolynomial α β γ).coeff 0 = X 1 ^ α * X 0 := by
    simp [loopSplitPolynomial_coeff, hγ0]
  have hc1 : (loopSplitPolynomial α β γ).coeff 1 = X 0 ^ β := by
    simp [loopSplitPolynomial_coeff, hγ1]
  have hcγ : (loopSplitPolynomial α β γ).coeff γ = X 1 := by
    simp [loopSplitPolynomial_coeff, hγ0, Ne.symm hγ1]
  apply Polynomial.irreducible_of_eisenstein_criterion
      ((Ideal.span_singleton_prime (X_ne_zero 0)).mpr hx)
  · rw [loopSplitPolynomial_leadingCoeff α β γ hγ, Ideal.mem_span_singleton]
    simpa using mv_X_not_dvd_other_pow (0 : Fin 2) 1 (by decide) 1
  · intro n hn
    rw [loopSplitPolynomial_degree α β γ hγ] at hn
    have hne : γ ≠ n := by exact_mod_cast (ne_of_gt hn)
    rw [loopSplitPolynomial_coeff]
    simp only [hne, ↓reduceIte, zero_add]
    apply Ideal.add_mem
    · split_ifs
      · exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) β (by omega)
      · exact Ideal.zero_mem _
    · split_ifs
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · exact Ideal.zero_mem _
  · rw [loopSplitPolynomial_degree α β γ hγ]
    exact_mod_cast (show 0 < γ by omega)
  · rw [hc0, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
    intro h
    have hh : (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ∣ X 1 ^ α :=
      (mul_dvd_mul_iff_right (X_ne_zero 0)).mp h
    exact mv_X_not_dvd_other_pow 0 1 (by decide) α hh
  · apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
    intro r hr
    have hd := (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr
    have hdy : r ∣ X (1 : Fin 2) := hcγ ▸ hd γ
    rcases hy.irreducible.dvd_iff.mp hdy with hu | hassoc
    · exact hu
    · exfalso
      exact mv_X_not_dvd_other_pow 1 0 (by decide) β
        (hassoc.dvd.trans (hc1 ▸ hd 1))

theorem loopPresentedRing_isDomain (α β γ : ℕ) (hβ : 1 ≤ β) (hγ : 2 ≤ γ) :
    IsDomain (PresentedRing (candidateRelation ⟨.V,α,β,γ⟩)) := by
  have hf : Prime (finSuccEquiv ℂ 2 (loopReverseRelation α β γ)) := by
    rw [finSuccEquiv_loopReverseRelation]
    exact (loopSplitPolynomial_irreducible α β γ hβ hγ).prime
  letI := AdjoinRoot.isDomain_of_prime hf
  letI : IsDomain (PresentedRing (loopReverseRelation α β γ)) :=
    (presentedAdjoinEquiv (loopReverseRelation α β γ)).toRingEquiv.toMulEquiv.isDomain _
  rw [loop_relation_reversed]
  exact (presentedRenameEquiv (loopReverseRelation α β γ) (Equiv.swap 0 2)).symm.toRingEquiv.toMulEquiv.isDomain _

end CanonicalRoots
