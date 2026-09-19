import CanonicalRoots.CoxCandidateRoot
import CanonicalRoots.DegreeUniversal

noncomputable section
namespace CanonicalRoots

/-- Primitive candidate weights detect the root in any additive quotient of the degree group. -/
theorem candidate_root_annihilated {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ)
    {H : Type*} [AddCommGroup H] (φ : DegreeGroup (candidateSignature e) →+ H)
    (hφ : ∀ i, φ (candidateMonomialDegree e i) = 0) : φ τ = 0 := by
  have hw (i : Fin 3) : candidateWeights e i • φ τ = 0 := by
    rw [← map_zsmul, ← candidate_monomial_degrees ha he τ hτ i, hφ]
  obtain ⟨v,hv⟩ := primitive_three_bezout (candidateWeights e) he.2.2.2.1
  calc
    φ τ = (1 : ℤ) • φ τ := by simp
    _ = (∑ i, v i * candidateWeights e i) • φ τ := by rw [hv]
    _ = ∑ i, v i • (candidateWeights e i • φ τ) := by simp only [Finset.sum_smul, mul_smul]
    _ = 0 := by simp only [hw, smul_zero, Finset.sum_const_zero]

theorem chain_residue_relations {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (i : Fin 3) :
    (candidateSignature ⟨.IV,α,β,γ⟩ i : ℤ) • (![-1,-(α : ZMod (α * γ)),1] i) = -α := by
  have hm : (α : ZMod (α * γ)) * γ = 0 := by rw [← Nat.cast_mul, ZMod.natCast_self]
  rw [candidateSignature_cast he]
  fin_cases i <;> simp [Cox.signature, zsmul_eq_mul] <;>
    first | linear_combination -(β - (1 : ZMod (α * γ))) * hm
          | linear_combination (β - (1 : ZMod (α * γ))) * hm
          | linear_combination hm | linear_combination -hm

def chainDegreeResidue {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩) :
    DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩) →+ ZMod (α * γ) :=
  degreeLift _ ![-1,-α,1] (-α) (chain_residue_relations he)

theorem chainDegreeResidue_monomial {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (i : Fin 3) : chainDegreeResidue he (candidateMonomialDegree ⟨.IV,α,β,γ⟩ i) = 0 := by
  have hm : (α : ZMod (α * γ)) * γ = 0 := by rw [← Nat.cast_mul, ZMod.natCast_self]
  fin_cases i <;> simp [chainDegreeResidue, candidateMonomialDegree, Fin.sum_univ_three,
    Cox.monomials, zsmul_eq_mul] <;> first | linear_combination hm | linear_combination -hm

theorem chainDegreeResidue_root {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) : chainDegreeResidue he τ = 0 :=
  candidate_root_annihilated ha he τ hτ (chainDegreeResidue he) (chainDegreeResidue_monomial he)

/-- The chain congruence uses primitive weights, so it also applies when a and gamma share a factor. -/
theorem chain_root_monomial_divisibility {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) (d : Fin 3 →₀ ℕ)
    (hd : ∃ m : ℕ, Finsupp.weight (xDegree (candidateSignature ⟨.IV,α,β,γ⟩)) d = m • τ) :
    ((α * γ : ℕ) : ℤ) ∣ (d 2 : ℤ) - d 0 - α * d 1 := by
  obtain ⟨m,hm⟩ := hd
  have hh := congrArg (chainDegreeResidue he) hm
  rw [map_nsmul, chainDegreeResidue_root ha he τ hτ, smul_zero] at hh
  have heq : ((d 2 : ℤ) - d 0 - α * d 1 : ZMod (α * γ)) = 0 := by
    simpa [chainDegreeResidue, Finsupp.weight_eq_sum, Fin.sum_univ_three,
      nsmul_eq_mul, sub_eq_add_neg, mul_comm, add_comm, add_left_comm, add_assoc] using hh
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using heq)

end CanonicalRoots
