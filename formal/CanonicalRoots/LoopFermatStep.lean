import CanonicalRoots.LoopExponentReduction
import CanonicalRoots.CoxCandidateMonomials

noncomputable section
namespace CanonicalRoots

theorem loop_signature_nat {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩) :
    candidateSignature ⟨.V,α,β,γ⟩ = ![β * (α - 1) + 1, γ * (β - 1) + 1, α * (γ - 1) + 1] := by
  have ha : 1 ≤ α := by have ha : 2 ≤ α := he.1; omega
  have hb : 1 ≤ β := by have hb : 2 ≤ β := he.2.1; omega
  have hc : 1 ≤ γ := by have hc : 2 ≤ γ := he.2.2.1; omega
  ext i
  have hh : (candidateSignature ⟨.V,α,β,γ⟩ i : ℤ) =
      (![β * (α - 1) + 1, γ * (β - 1) + 1, α * (γ - 1) + 1] i : ℕ) := by
    rw [candidateSignature_cast he]
    fin_cases i <;> simp [Cox.signature, Nat.cast_sub ha, Nat.cast_sub hb, Nat.cast_sub hc]
  exact_mod_cast hh

theorem loop_signature_thresholds {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩) :
    candidateSignature ⟨.V,α,β,γ⟩ 0 + β = α * β + 1 ∧
    candidateSignature ⟨.V,α,β,γ⟩ 1 + γ = β * γ + 1 ∧
    candidateSignature ⟨.V,α,β,γ⟩ 2 + α = γ * α + 1 := by
  have ha : 1 ≤ α := by have hh : 2 ≤ α := he.1; omega
  have hb : 1 ≤ β := by have hh : 2 ≤ β := he.2.1; omega
  have hc : 1 ≤ γ := by have hh : 2 ≤ γ := he.2.2.1; omega
  simp only [loop_signature_nat he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  dsimp
  constructor
  · nlinarith [Nat.sub_add_cancel ha]
  constructor
  · nlinarith [Nat.sub_add_cancel hb]
  · change α * (γ - 1) + 1 + α = γ * α + 1
    nlinarith [Nat.sub_add_cancel hc]

theorem loop_signature_bounds {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩) :
    β ≤ candidateSignature ⟨.V,α,β,γ⟩ 0 ∧
    γ ≤ candidateSignature ⟨.V,α,β,γ⟩ 1 ∧
    α ≤ candidateSignature ⟨.V,α,β,γ⟩ 2 := by
  have ha : 2 ≤ α := he.1
  have hb : 2 ≤ β := he.2.1
  have hc : 2 ≤ γ := he.2.2.1
  obtain ⟨h0,h1,h2⟩ := loop_signature_thresholds he
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Each nonzero lattice monomial either contains a Cox factor or reduces to terms containing one. -/
theorem loop_exponent_fermat_step {a α β γ : ℕ} (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (d : Fin 3 →₀ ℕ) (hd : LoopCongruence α β γ (d 0) (d 1) (d 2)) :
    d = 0 ∨ (∃ i, candidateMonomialExponent ⟨.V,α,β,γ⟩ i ≤ d) ∨
    (∃ i t, d = t + Finsupp.single i (candidateSignature ⟨.V,α,β,γ⟩ i) ∧
      ∀ j, j ≠ i → ∃ k, candidateMonomialExponent ⟨.V,α,β,γ⟩ k ≤
        t + Finsupp.single j (candidateSignature ⟨.V,α,β,γ⟩ j)) := by
  have ha : 2 ≤ α := he.1
  have hb : 2 ≤ β := he.2.1
  have hc : 2 ≤ γ := he.2.2.1
  obtain ⟨hp0,hp1,hp2⟩ := loop_signature_bounds he
  obtain ⟨ht0,ht1,ht2⟩ := loop_signature_thresholds he
  rcases loop_exponent_reduction_cases ha hb hc hd with hz | h0 | h1 | h2 | h0 | h1 | h2
  · apply Or.inl
    ext i
    fin_cases i <;> simp [hz.1,hz.2.1,hz.2.2]
  · apply Or.inr ∘ Or.inl
    refine ⟨0, ?_⟩
    intro i
    fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
  · apply Or.inr ∘ Or.inl
    refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
  · apply Or.inr ∘ Or.inl
    refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
  · have hs : β ≤ d 0 - candidateSignature ⟨.V,α,β,γ⟩ 0 := by omega
    have hle : Finsupp.single 0 (candidateSignature ⟨.V,α,β,γ⟩ 0) ≤ d := by
      intro i
      fin_cases i <;> simp <;> omega
    apply Or.inr ∘ Or.inr
    refine ⟨0,d - Finsupp.single 0 (candidateSignature ⟨.V,α,β,γ⟩ 0),
      (tsub_add_cancel_of_le hle).symm, ?_⟩
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · refine ⟨1, ?_⟩
      intro i
      fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
    · refine ⟨0, ?_⟩
      intro i
      fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
  · have hs : γ ≤ d 1 - candidateSignature ⟨.V,α,β,γ⟩ 1 := by omega
    have hle : Finsupp.single 1 (candidateSignature ⟨.V,α,β,γ⟩ 1) ≤ d := by
      intro i
      fin_cases i <;> simp <;> omega
    apply Or.inr ∘ Or.inr
    refine ⟨1,d - Finsupp.single 1 (candidateSignature ⟨.V,α,β,γ⟩ 1),
      (tsub_add_cancel_of_le hle).symm, ?_⟩
    intro j hj
    fin_cases j
    · refine ⟨1, ?_⟩
      intro i
      fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
    · exact (hj rfl).elim
    · refine ⟨2, ?_⟩
      intro i
      fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
  · have hs : α ≤ d 2 - candidateSignature ⟨.V,α,β,γ⟩ 2 := by omega
    have hle : Finsupp.single 2 (candidateSignature ⟨.V,α,β,γ⟩ 2) ≤ d := by
      intro i
      fin_cases i <;> simp <;> omega
    apply Or.inr ∘ Or.inr
    refine ⟨2,d - Finsupp.single 2 (candidateSignature ⟨.V,α,β,γ⟩ 2),
      (tsub_add_cancel_of_le hle).symm, ?_⟩
    intro j hj
    fin_cases j
    · refine ⟨0, ?_⟩
      intro i
      fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
    · refine ⟨2, ?_⟩
      intro i
      fin_cases i <;> simp [candidateMonomialExponent,Cox.monomials] <;> omega
    · exact (hj rfl).elim

end CanonicalRoots
