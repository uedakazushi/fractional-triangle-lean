import CanonicalRoots.CoxRootResidue

noncomputable section
namespace CanonicalRoots

theorem loop_residue_relations {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (i : Fin 3) :
    (candidateSignature ⟨.V,α,β,γ⟩ i : ℤ) •
      (![(γ : ZMod (α * β * γ + 1)), -1, -(β * γ)] i) =
        (γ : ZMod (α * β * γ + 1)) - 1 - β * γ := by
  have hm : (α : ZMod (α * β * γ + 1)) * β * γ + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using ZMod.natCast_self (α * β * γ + 1)
  rw [candidateSignature_cast he]
  fin_cases i
  · simp [Cox.signature, zsmul_eq_mul]
    linear_combination hm
  · simp [Cox.signature, zsmul_eq_mul]
    ring
  · simp [Cox.signature, zsmul_eq_mul]
    linear_combination (1 - (γ : ZMod (α * β * γ + 1))) * hm

def loopDegreeResidue {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩) :
    DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩) →+ ZMod (α * β * γ + 1) :=
  degreeLift _ ![γ,-1,-(β * γ)] ((γ : ZMod (α * β * γ + 1)) - 1 - β * γ) (loop_residue_relations he)

theorem loopDegreeResidue_monomial {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (i : Fin 3) : loopDegreeResidue he (candidateMonomialDegree ⟨.V,α,β,γ⟩ i) = 0 := by
  have hm : (α : ZMod (α * β * γ + 1)) * β * γ + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using ZMod.natCast_self (α * β * γ + 1)
  fin_cases i <;> simp [loopDegreeResidue, candidateMonomialDegree, Fin.sum_univ_three,
    Cox.monomials] <;> linear_combination -hm

theorem loopDegreeResidue_root {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) : loopDegreeResidue he τ = 0 :=
  candidate_root_annihilated ha he τ hτ (loopDegreeResidue he) (loopDegreeResidue_monomial he)

theorem loop_root_monomial_divisibility {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) (d : Fin 3 →₀ ℕ)
    (hd : ∃ m : ℕ, Finsupp.weight (xDegree (candidateSignature ⟨.V,α,β,γ⟩)) d = m • τ) :
    ((α * β * γ + 1 : ℕ) : ℤ) ∣ γ * (d 0 : ℤ) - d 1 - β * γ * d 2 := by
  obtain ⟨m,hm⟩ := hd
  have hh := congrArg (loopDegreeResidue he) hm
  rw [map_nsmul, loopDegreeResidue_root ha he τ hτ, smul_zero] at hh
  have heq : ((γ : ℤ) * d 0 - d 1 - β * γ * d 2 : ZMod (α * β * γ + 1)) = 0 := by
    simpa [loopDegreeResidue, Finsupp.weight_eq_sum, Fin.sum_univ_three,
      nsmul_eq_mul, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hh
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using heq)

end CanonicalRoots
