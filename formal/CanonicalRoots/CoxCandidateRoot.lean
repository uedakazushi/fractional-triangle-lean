import CanonicalRoots.CoxCandidateSignature
import CanonicalRoots.CoxDegrees
import CanonicalRoots.RootArithmetic

noncomputable section
namespace CanonicalRoots

/-- Three-variable Bezout coefficients from mathlib's two-variable gcd identities. -/
theorem primitive_three_bezout (w : Fin 3 → ℤ)
    (hw : Int.gcd (w 0) (Int.gcd (w 1) (w 2)) = 1) :
    ∃ v : Fin 3 → ℤ, ∑ i, v i * w i = 1 := by
  let d : ℤ := Int.gcd (w 1) (w 2)
  have h0 := Int.gcd_eq_gcd_ab (w 0) d
  have h1 := Int.gcd_eq_gcd_ab (w 1) (w 2)
  change (Int.gcd (w 0) (Int.gcd (w 1) (w 2)) : ℤ) = _ at h0
  rw [hw] at h0
  refine ⟨![Int.gcdA (w 0) d,
    Int.gcdB (w 0) d * Int.gcdA (w 1) (w 2),
    Int.gcdB (w 0) d * Int.gcdB (w 1) (w 2)], ?_⟩
  simp [Fin.sum_univ_three]
  change d = _ at h1
  linear_combination -h0 - Int.gcdB (w 0) d * h1

/-- Primitive weights turn multiplied degree certificates into an actual group root. -/
theorem primitive_three_degree_root {G : Type*} [AddCommGroup G]
    (a : ℕ) (w : Fin 3 → ℤ) (y : Fin 3 → G) (ω : G)
    (hw : Int.gcd (w 0) (Int.gcd (w 1) (w 2)) = 1)
    (hy : ∀ i, a • y i = w i • ω) : ∃ τ : G, a • τ = ω := by
  obtain ⟨v, hv⟩ := primitive_three_bezout w hw
  refine ⟨∑ i, v i • y i, ?_⟩
  calc
    a • ∑ i, v i • y i = ∑ i, v i • (a • y i) := by simp only [Finset.smul_sum, smul_comm a]
    _ = ∑ i, (v i * w i) • ω := by simp only [hy, mul_smul]
    _ = (∑ i, v i * w i) • ω := (Finset.sum_smul ..).symm
    _ = ω := by rw [hv]; simp

def candidateMonomialDegree (e : TernaryCandidate) (i : Fin 3) : DegreeGroup (candidateSignature e) :=
  ∑ j, Cox.monomials e.kind e.alpha e.beta e.gamma i j • xDegree (candidateSignature e) j

/-- The integer Cox certificates hold in the actual, torsion-retaining degree group. -/
theorem candidate_monomial_degree_identity {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (i : Fin 3) :
    a • candidateMonomialDegree e i = candidateWeights e i • omegaDegree (candidateSignature e) := by
  have h := Cox.lattice_degree e.kind e.alpha e.beta e.gamma (xDegree (candidateSignature e))
    (cDegree (candidateSignature e)) (fun j => by
      rw [← candidateSignature_cast he j]
      exact degree_relation (candidateSignature e) j) i
  rw [he.2.2.2.2] at h
  exact h

/-- Every positive arithmetic candidate has its unique actual canonical root. -/
theorem candidate_root_exists_unique {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    ∃! τ : DegreeGroup (candidateSignature e), IsCanonicalRoot (candidateSignature e) a τ := by
  obtain ⟨τ, hτ⟩ := primitive_three_degree_root a (candidateWeights e) (candidateMonomialDegree e)
    (omegaDegree (candidateSignature e)) he.2.2.2.1 (candidate_monomial_degree_identity he)
  have hp (i : Fin 3) : 0 < candidateSignature e i := by have := candidateSignature_ge_two he i; omega
  exact ⟨τ, hτ, fun σ hσ => canonicalRoot_unique _ hp (by omega) σ τ hσ hτ⟩

/-- Cancellation is justified by the actual root equation and its coprimality theorem. -/
theorem candidate_monomial_degrees {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (i : Fin 3) :
    candidateMonomialDegree e i = candidateWeights e i • τ := by
  have hp (j : Fin 3) : 0 < candidateSignature e j := by have := candidateSignature_ge_two he j; omega
  apply degree_nsmul_injective _ hp (by omega : 0 < a) (canonicalRoot_coprime _ hp τ hτ)
  change a • candidateMonomialDegree e i = a • (candidateWeights e i • τ)
  rw [candidate_monomial_degree_identity he i, smul_comm a, hτ]

end CanonicalRoots
