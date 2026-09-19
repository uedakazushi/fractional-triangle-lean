import CanonicalRoots.CandidateData
import CanonicalRoots.CoxScaledMultiplicity

namespace CanonicalRoots.Cox

theorem signature_ge_two (kind : Kind) (α β γ : ℤ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (i : Fin 3) : 2 ≤ signature kind α β γ i := by
  have hab : 2 ≤ β * (α - 1) + 1 := by nlinarith [mul_nonneg (by omega : 0 ≤ β - 2) (by omega : 0 ≤ α - 2)]
  have hbc : 2 ≤ γ * (β - 1) := by nlinarith [mul_nonneg (by omega : 0 ≤ γ - 2) (by omega : 0 ≤ β - 2)]
  have hca : 2 ≤ α * (γ - 1) := by nlinarith [mul_nonneg (by omega : 0 ≤ α - 2) (by omega : 0 ≤ γ - 2)]
  have hac : 2 ≤ γ * (α - 1) := by nlinarith [mul_nonneg (by omega : 0 ≤ γ - 2) (by omega : 0 ≤ α - 2)]
  cases kind <;> fin_cases i <;> simp [signature] <;> omega

end CanonicalRoots.Cox

namespace CanonicalRoots

def candidateSignature (e : TernaryCandidate) : Fin 3 → ℕ :=
  fun i => (Cox.signature e.kind e.alpha e.beta e.gamma i).toNat

theorem candidateSignature_cast {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) (i : Fin 3) :
    (candidateSignature e i : ℤ) = Cox.signature e.kind e.alpha e.beta e.gamma i := by
  apply Int.toNat_of_nonneg
  have := Cox.signature_ge_two e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) i
  omega

theorem candidateSignature_ge_two {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) (i : Fin 3) :
    2 ≤ candidateSignature e i := by
  have hc := candidateSignature_cast he i
  have := Cox.signature_ge_two e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) i
  omega

/-- The actual signature table is admissible for every positive arithmetic candidate. -/
theorem candidateSignature_admissible {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) : AdmissibleSignature (candidateSignature e) := by
  have hα : (2 : ℤ) ≤ e.alpha := by exact_mod_cast he.1
  have hβ : (2 : ℤ) ≤ e.beta := by exact_mod_cast he.2.1
  have hγ : (2 : ℤ) ≤ e.gamma := by exact_mod_cast he.2.2.1
  have hw (i : Fin 3) : (0 : ℚ) < Cox.weights e.kind e.alpha e.beta e.gamma i := by
    exact_mod_cast Cox.weights_pos e.kind e.alpha e.beta e.gamma hα hβ hγ i
  have hp (i : Fin 3) : (0 : ℚ) < candidateSignature e i := by
    have := candidateSignature_ge_two he i
    exact_mod_cast (by omega : 0 < candidateSignature e i)
  have hd : (0 : ℚ) < Cox.degree e.kind e.alpha e.beta e.gamma := by
    exact_mod_cast Cox.degree_pos e.kind e.alpha e.beta e.gamma hα hβ hγ
  have hm := Cox.scaled_signature_defect e.kind e.alpha e.beta e.gamma
    (fun i => (Cox.weights e.kind e.alpha e.beta e.gamma i : ℚ))
    (fun i => (candidateSignature e i : ℚ)) a (Cox.degree e.kind e.alpha e.beta e.gamma) 1
    (fun i => ne_of_gt (hw i)) (fun i => ne_of_gt (hp i)) (by norm_num)
    (by intro i; simp) (by intro i; simp only [one_mul]; exact_mod_cast (candidateSignature_cast he i).symm)
    (by simp) (by simp only [one_mul]; exact_mod_cast he.2.2.2.2)
  have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hprod : (0 : ℚ) < ∏ i, (Cox.weights e.kind e.alpha e.beta e.gamma i : ℚ) :=
    Finset.prod_pos (fun i _ => hw i)
  have hpos : (0 : ℚ) < (a : ℚ) * (Cox.degree e.kind e.alpha e.beta e.gamma / ∏ i, (Cox.weights e.kind e.alpha e.beta e.gamma i : ℚ)) :=
    mul_pos hapos (div_pos hd hprod)
  exact ⟨candidateSignature_ge_two he, by linarith⟩

end CanonicalRoots
