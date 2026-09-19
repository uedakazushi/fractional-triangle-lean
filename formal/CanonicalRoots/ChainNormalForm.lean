import CanonicalRoots.ChainLeadingMonomials
import CanonicalRoots.BoundedAmbientInjection
import CanonicalRoots.CoxMonicInjection

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem chainReductionTail_degreeOf_two (α β γ : ℕ) :
    (chainReductionTail α β γ).degreeOf 2 = 0 := by
  rw [chainReductionTail, degreeOf_neg]
  apply Nat.eq_zero_of_le_zero
  apply (degreeOf_add_le _ _ _).trans
  simp [degreeOf_X_pow_of_ne]

theorem chainReducedMonomial_degreeOf_two {α β γ : ℕ} (hα : 0 < α) (hγ : 2 ≤ γ)
    (d : Fin 3 →₀ ℕ) : (chainReducedMonomial α β γ d).degreeOf 2 = d 0 % α := by
  have hn (n : ℕ) (i : Fin 3) : (X i ^ n : MvPolynomial (Fin 3) ℂ) ≠ 0 :=
    pow_ne_zero _ (X_ne_zero _)
  have ht := chainReductionTail_ne_zero (β := β) hα hγ
  rw [chainReducedMonomial, degreeOf_mul_eq (mul_ne_zero (mul_ne_zero (hn _ _) (hn _ _)) (hn _ _))
    (pow_ne_zero _ ht), degreeOf_mul_eq (mul_ne_zero (hn _ _) (hn _ _)) (hn _ _),
    degreeOf_mul_eq (hn _ _) (hn _ _), degreeOf_pow_eq _ _ _ ht,
    chainReductionTail_degreeOf_two]
  simp [degreeOf_X_pow_of_ne]

/-- Polynomial reduction agrees with the original image in the actual Fermat quotient. -/
theorem chainReducedMonomial_quotient {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (d : Fin 3 →₀ ℕ) :
    ambientQuotient (candidateSignature ⟨.IV,α,β,γ⟩)
      (rename (Equiv.swap (0 : Fin 3) 2) (chainReducedMonomial α β γ d)) =
    ambientQuotient (candidateSignature ⟨.IV,α,β,γ⟩)
      (monomial (candidateExponentMap ⟨.IV,α,β,γ⟩ d) 1) := by
  let q := ambientQuotient (candidateSignature ⟨.IV,α,β,γ⟩)
  have hF : q (fermat (candidateSignature ⟨.IV,α,β,γ⟩)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [congrArg fermat (chain_signature_nat he)] at hF
  simp only [fermat, Fin.sum_univ_three, map_add, map_pow] at hF
  dsimp at hF
  have hred : q (rename (Equiv.swap (0 : Fin 3) 2) (chainReductionTail α β γ)) = q (X 0) ^ α := by
    simp only [chainReductionTail, map_neg, map_add, map_pow, rename_X]
    norm_num [Equiv.swap_apply_def]
    linear_combination -hF
  change q _ = q _
  simp only [chainReducedMonomial, map_mul, map_pow]
  rw [hred]
  simp only [rename_X]
  norm_num [Equiv.swap_apply_def]
  have he0 : candidateExponentMap ⟨.IV,α,β,γ⟩ d 0 = d 0 := by
    simp [candidateExponentMap, candidateMonomialExponent, Cox.monomials, Fin.sum_univ_three]
  have he1 : candidateExponentMap ⟨.IV,α,β,γ⟩ d 1 = γ * d 1 + d 2 := by
    simp [candidateExponentMap, candidateMonomialExponent, Cox.monomials, Fin.sum_univ_three, Nat.mul_comm]
  have he2 : candidateExponentMap ⟨.IV,α,β,γ⟩ d 2 = d 0 + α * d 2 := by
    simp [candidateExponentMap, candidateMonomialExponent, Cox.monomials, Fin.sum_univ_three, Nat.mul_comm]
  rw [monomial_three, he0, he1, he2]
  simp only [map_mul, map_pow, ← pow_mul]
  calc
    _ = q (X 0) ^ (d 0 % α + α * (d 0 / α)) *
        q (X 1) ^ (γ * d 1 + d 2) * q (X 2) ^ (d 0 + α * d 2) := by
      rw [pow_add]
      ring
    _ = _ := by rw [Nat.mod_add_div]

theorem chainReducedQuotient_linearIndependent {a α β γ : ℕ}
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩) :
    LinearIndependent ℂ (fun d : {d : Fin 3 →₀ ℕ // d 2 < γ} =>
      ambientQuotient (candidateSignature ⟨.IV,α,β,γ⟩)
        (monomial (candidateExponentMap ⟨.IV,α,β,γ⟩ d.val) 1)) := by
  have hα : 0 < α := by have hh : 2 ≤ α := he.1; omega
  have hγ : 2 ≤ γ := he.2.2.1
  have hp : candidateSignature ⟨.IV,α,β,γ⟩ 0 = α := by simp [chain_signature_nat he]
  have hli : LinearIndependent ℂ (fun d : {d : Fin 3 →₀ ℕ // d 2 < γ} =>
      rename (Equiv.swap (0 : Fin 3) 2) (chainReducedMonomial α β γ d.val)) :=
    (chainReducedMonomials_linearIndependent (β := β) hα hγ).map'
      (renameEquiv ℂ (Equiv.swap (0 : Fin 3) 2)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (renameEquiv ℂ (Equiv.swap (0 : Fin 3) 2)).injective)
  have hh := ambientQuotient_linearIndependent_of_bounded (candidateSignature ⟨.IV,α,β,γ⟩)
    (by rw [hp]; exact hα) _ hli (fun d => ?_)
  · simpa only [chainReducedMonomial_quotient he] using hh
  · rw [hp]
    have hdeg := degreeOf_rename_of_injective (p := chainReducedMonomial α β γ d.val)
      (Equiv.swap (0 : Fin 3) 2).injective 2
    rw [Equiv.swap_apply_right, chainReducedMonomial_degreeOf_two hα hγ] at hdeg
    exact hdeg.trans_lt (Nat.mod_lt _ hα)

end CanonicalRoots
