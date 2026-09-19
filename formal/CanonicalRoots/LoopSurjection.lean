import CanonicalRoots.LoopFermatStep
import CanonicalRoots.WeightedFermatGeneration
import CanonicalRoots.PermutedRootMonomials
import CanonicalRoots.HigherRealization

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def loopExponentResidue {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩) :
    (Fin 3 →₀ ℕ) →+ ZMod (α * β * γ + 1) :=
  (loopDegreeResidue he).comp (Finsupp.weight (xDegree (candidateSignature ⟨.V,α,β,γ⟩)))

theorem loopExponentResidue_zero_iff {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (d : Fin 3 →₀ ℕ) : loopExponentResidue he d = 0 ↔ LoopCongruence α β γ (d 0) (d 1) (d 2) := by
  have hh : loopExponentResidue he d =
      (((γ : ℤ) * d 0 - d 1 - β * γ * d 2 : ℤ) : ZMod (α * β * γ + 1)) := by
    simp [loopExponentResidue, loopDegreeResidue, Finsupp.weight_eq_sum,
      Fin.sum_univ_three, nsmul_eq_mul, sub_eq_add_neg,
      mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
  rw [hh, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

theorem loopExponentResidue_generator {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (i : Fin 3) : loopExponentResidue he (candidateMonomialExponent ⟨.V,α,β,γ⟩ i) = 0 := by
  change loopDegreeResidue he (Finsupp.weight _ _) = 0
  rw [candidateMonomialExponent_degree he, loopDegreeResidue_monomial he]

theorem loopExponentResidue_fermat {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (i j : Fin 3) :
    loopExponentResidue he (Finsupp.single i (candidateSignature ⟨.V,α,β,γ⟩ i)) =
      loopExponentResidue he (Finsupp.single j (candidateSignature ⟨.V,α,β,γ⟩ j)) := by
  simp only [loopExponentResidue, AddMonoidHom.comp_apply, Finsupp.weight_single]
  congr 1
  exact (degree_relation _ i).trans (degree_relation _ j).symm

theorem loop_generator_weight_pos (α β γ : ℕ) (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (i : Fin 3) : 0 < Finsupp.weight w (candidateMonomialExponent ⟨.V,α,β,γ⟩ i) := by
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  fin_cases i <;> simp [Finsupp.weight_eq_sum, Fin.sum_univ_three,
    candidateMonomialExponent, Cox.monomials, nsmul_eq_mul] <;> omega

/-- The three loop Cox monomials generate every residue-zero monomial after the Fermat relation. -/
theorem loop_polynomial_preimage {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ)
    (d : Fin 3 →₀ ℕ) (hd : LoopCongruence α β γ (d 0) (d 1) (d 2)) :
    ∃ f : MvPolynomial (Fin 3) ℂ,
      (candidatePolynomialMap ha he τ hτ f : AmbientRing (candidateSignature ⟨.V,α,β,γ⟩)) =
        ambientQuotient (candidateSignature ⟨.V,α,β,γ⟩) (monomial d 1) := by
  let p := candidateSignature ⟨.V,α,β,γ⟩
  let φ := (rootSubalgebra p τ).val.comp (candidatePolynomialMap ha he τ hτ)
  let w := productWeights p
  have hp : ∀ i, 0 < p i := fun i => by
    dsimp [p]
    have := candidateSignature_ge_two he i
    omega
  apply fermat_monomial_generation_of_step p w (loopExponentResidue he)
    (candidateMonomialExponent ⟨.V,α,β,γ⟩) φ.range
  · intro i
    refine ⟨X i, ?_⟩
    change ((rootSubalgebra p τ).val.comp (candidatePolynomialMap ha he τ hτ)) (X i) = _
    rw [candidatePolynomialMap_val]
    simp [candidateMonomial, p]
  · exact loop_generator_weight_pos α β γ w (productWeights_pos p hp)
  · exact loopExponentResidue_generator he
  · intro i j
    simp only [Finsupp.weight_single, smul_eq_mul, w, Nat.mul_comm (p i), Nat.mul_comm (p j),
      productWeights_mul]
  · exact loopExponentResidue_fermat he
  · intro b hb
    exact loop_exponent_fermat_step he b ((loopExponentResidue_zero_iff he b).mp hb)
  · exact (loopExponentResidue_zero_iff he d).mpr hd

/-- Type V Cox generators generate the entire actual canonical-root ring. -/
theorem candidateQuotientMap_surjective_loop {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) :
    Function.Surjective (candidateQuotientMap ha he τ hτ) := by
  apply rootMap_surjective_of_permuted_monomials (candidateSignature ⟨.V,α,β,γ⟩)
    (Equiv.refl _) (by have := candidateSignature_ge_two he 0; simpa using (show 0 < candidateSignature ⟨.V,α,β,γ⟩ 0 by omega)) τ
  intro d _ hd
  obtain ⟨f,hf⟩ := loop_polynomial_preimage ha he τ hτ d
    (loop_root_monomial_divisibility ha he τ hτ d hd)
  refine ⟨(Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.V,α,β,γ⟩})) f, ?_⟩
  rw [candidateQuotientMap_mk]
  exact hf

end CanonicalRoots
