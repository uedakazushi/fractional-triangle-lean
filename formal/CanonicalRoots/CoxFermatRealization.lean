import CanonicalRoots.CoxCandidateHomogeneous
import CanonicalRoots.HigherRealization

noncomputable section
namespace CanonicalRoots

/-- Primitive three pair-products force the three factors to be pairwise coprime. -/
theorem coprime_of_pair_products_primitive (α β γ : ℕ)
    (hg : Nat.gcd (β * γ) (Nat.gcd (α * γ) (α * β)) = 1) :
    Nat.Coprime α β ∧ Nat.Coprime α γ ∧ Nat.Coprime β γ := by
  have hAB : Nat.gcd α β ∣ Nat.gcd (β * γ) (Nat.gcd (α * γ) (α * β)) :=
    Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_right α β) γ)
      (Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left α β) γ)
        (dvd_mul_of_dvd_left (Nat.gcd_dvd_left α β) β))
  have hAC : Nat.gcd α γ ∣ Nat.gcd (β * γ) (Nat.gcd (α * γ) (α * β)) :=
    Nat.dvd_gcd (dvd_mul_of_dvd_right (Nat.gcd_dvd_right α γ) β)
      (Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left α γ) γ)
        (dvd_mul_of_dvd_left (Nat.gcd_dvd_left α γ) β))
  have hBC : Nat.gcd β γ ∣ Nat.gcd (β * γ) (Nat.gcd (α * γ) (α * β)) :=
    Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left β γ) γ)
      (Nat.dvd_gcd (dvd_mul_of_dvd_right (Nat.gcd_dvd_right β γ) α)
        (dvd_mul_of_dvd_right (Nat.gcd_dvd_left β γ) α))
  rw [hg] at hAB hAC hBC
  exact ⟨Nat.dvd_one.mp hAB, Nat.dvd_one.mp hAC, Nat.dvd_one.mp hBC⟩

theorem productWeights_three (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) (i : Fin 3) :
    productWeights p i = ![p 1 * p 2, p 0 * p 2, p 0 * p 1] i := by
  apply Nat.eq_of_mul_eq_mul_left (hp i)
  rw [Nat.mul_comm (p i), productWeights_mul]
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

theorem fermat_candidate_coprime {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.I,α,β,γ⟩) :
    Pairwise (fun i j => Nat.Coprime (candidateSignature ⟨.I,α,β,γ⟩ i)
      (candidateSignature ⟨.I,α,β,γ⟩ j)) := by
  have hg : Nat.gcd (β * γ) (Nat.gcd (α * γ) (α * β)) = 1 := by
    have hh := he.2.2.2.1
    simp only [candidateWeights, Cox.weights, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hh
    norm_cast at hh
  obtain ⟨hab,hac,hbc⟩ := coprime_of_pair_products_primitive α β γ hg
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [candidateSignature, Cox.signature] at hij ⊢ <;>
      first | exact hab | exact hac | exact hbc | exact hab.symm | exact hac.symm | exact hbc.symm

theorem candidateRelation_fermat (α β γ : ℕ) :
    candidateRelation ⟨.I,α,β,γ⟩ = fermat (candidateSignature ⟨.I,α,β,γ⟩) := by
  unfold candidateRelation fermat
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.X_pow_eq_monomial]
  apply congrArg (fun d => MvPolynomial.monomial d (1 : ℂ))
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [candidateRelationExponent, candidateSignature, Cox.exponents, Cox.signature]

theorem candidateNatWeights_fermat {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.I,α,β,γ⟩) :
    candidateNatWeights ⟨.I,α,β,γ⟩ = productWeights (candidateSignature ⟨.I,α,β,γ⟩) := by
  ext i
  rw [productWeights_three _ (fun j => by have := candidateSignature_ge_two he j; omega)]
  fin_cases i <;> simp [candidateNatWeights, candidateWeights, candidateSignature,
    Cox.weights, Cox.signature, Int.toNat_mul]

/-- Type I reuses the existing general coprime realization in dimension three. -/
theorem fermat_candidate_realization {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.I,α,β,γ⟩) :
    ∃ t : Target 3 a, t.signature = candidateSignature ⟨.I,α,β,γ⟩ ∧
      (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.I,α,β,γ⟩ i) ∧
      (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.I,α,β,γ⟩ ∧
      t.presentation.polynomial = candidateRelation ⟨.I,α,β,γ⟩ := by
  let e : TernaryCandidate := ⟨.I,α,β,γ⟩
  let p := candidateSignature e
  have hp : ∀ i, 2 ≤ p i := candidateSignature_ge_two he
  have hp0 : ∀ i, 0 < p i := fun i => by have := hp i; omega
  have hw (i : Fin 3) : (productWeights p i : ℤ) = candidateWeights e i := by
    rw [productWeights_three p hp0 i]
    fin_cases i <;> simp [p, e, candidateSignature, candidateWeights, Cox.signature, Cox.weights]
  have hd : ((∏ i, p i : ℕ) : ℤ) = candidateDegree e := by
    simp [p, e, candidateSignature, candidateDegree, Cox.signature, Cox.degree, Fin.prod_univ_three]
  have hdef : ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a := by
    rw [hd]
    simp only [hw]
    exact he.2.2.2.2
  have hc := fermat_candidate_coprime he
  obtain ⟨τ,hτ,_⟩ := higher_root_exists_unique p hp0 (by omega) hc hdef
  let P := higherRootPresentation (by decide : 0 < 3) p hp (by omega : 0 < a) hc hdef τ hτ
  let t : Target 3 a := ⟨by decide, ha, p, candidateSignature_admissible ha he, τ, hτ, P⟩
  exact ⟨t, rfl, hw, hd, (candidateRelation_fermat α β γ).symm⟩

/-- The type-I Cox equation is a graded presentation of each actual canonical root. -/
def fermatCandidatePresentation {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.I,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.I,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.I,α,β,γ⟩) a τ) :
    RootHypersurfacePresentation (candidateSignature ⟨.I,α,β,γ⟩) τ := by
  let e : TernaryCandidate := ⟨.I,α,β,γ⟩
  let p := candidateSignature e
  have hw := candidateNatWeights_fermat he
  have hd : candidateNatDegree e = ∏ i, p i := by
    simp only [candidateNatDegree, candidateDegree, p, e, candidateSignature,
      Cox.degree, Cox.signature, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]
    norm_cast
  have hdef : ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a := by
    rw [← hd, ← hw]
    simp only [candidateNatDegree_cast he, candidateNatWeights_cast he]
    exact he.2.2.2.2
  exact higherRootPresentation (by decide) p (candidateSignature_ge_two he)
    (by omega) (fermat_candidate_coprime he) hdef τ hτ

end CanonicalRoots
