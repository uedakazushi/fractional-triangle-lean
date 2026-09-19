import CanonicalRoots.CoxCandidateMap

noncomputable section
open CanonicalRoots

-- A root of index seven, with nontrivial degree-group data.
example : ArithmeticTernary 7 ⟨.V,2,3,5⟩ := by decide
example : candidateSignature ⟨.V,2,3,5⟩ = ![4,11,9] := by decide
example : AdmissibleSignature (candidateSignature ⟨.V,2,3,5⟩) :=
  candidateSignature_admissible (by decide : 1 ≤ 7) (by decide)
example : ∃! τ : DegreeGroup (candidateSignature ⟨.V,2,3,5⟩),
    IsCanonicalRoot (candidateSignature ⟨.V,2,3,5⟩) 7 τ :=
  candidate_root_exists_unique (by decide) (by decide)

-- Chain index two: the construction retains repeated signature entries.
example : ArithmeticTernary 2 ⟨.IV,3,4,2⟩ := by decide
example : candidateSignature ⟨.IV,3,4,2⟩ = ![3,7,3] := by decide
example : ∃! τ : DegreeGroup (candidateSignature ⟨.IV,3,4,2⟩),
    IsCanonicalRoot (candidateSignature ⟨.IV,3,4,2⟩) 2 τ :=
  candidate_root_exists_unique (by decide) (by decide)

-- This checks the actual quotient map interface, not just an integer certificate.
example {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ)
    (i : Fin 3) :
    candidateQuotientMap ha he τ hτ
      ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) (MvPolynomial.X i)) =
        candidateRootGenerator ha he τ hτ i := by
  rw [candidateQuotientMap_mk, candidatePolynomialMap_X]

example {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ)
    (i : Fin 3) :
    candidateRootGenerator ha he τ hτ i ∈ rootPiece (candidateSignature e) τ (candidateNatWeights e i) :=
  candidateRootGenerator_homogeneous ha he τ hτ i
