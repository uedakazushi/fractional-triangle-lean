import CanonicalRoots.CoxCandidateRoot

noncomputable section

namespace CanonicalRoots.Cox

theorem monomials_nonneg (kind : Kind) (α β γ : ℤ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (i j : Fin 3) : 0 ≤ monomials kind α β γ i j := by
  cases kind <;> fin_cases i <;> fin_cases j <;> simp [monomials] <;> omega

end CanonicalRoots.Cox

namespace CanonicalRoots

def candidateNatWeights (e : TernaryCandidate) (i : Fin 3) : ℕ := (candidateWeights e i).toNat

def candidateMonomialExponent (e : TernaryCandidate) (i : Fin 3) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (Cox.monomials e.kind e.alpha e.beta e.gamma i j).toNat)

def candidateMonomial (e : TernaryCandidate) (i : Fin 3) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.monomial (candidateMonomialExponent e i) 1

theorem candidateNatWeights_cast {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e) (i : Fin 3) :
    (candidateNatWeights e i : ℤ) = candidateWeights e i := by
  apply Int.toNat_of_nonneg
  exact le_of_lt (Cox.weights_pos e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) i)

theorem candidateMonomialExponent_cast {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (i j : Fin 3) : (candidateMonomialExponent e i j : ℤ) = Cox.monomials e.kind e.alpha e.beta e.gamma i j := by
  apply Int.toNat_of_nonneg
  exact Cox.monomials_nonneg e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1) i j

theorem candidateMonomialExponent_degree {a : ℕ} {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (i : Fin 3) : Finsupp.weight (xDegree (candidateSignature e)) (candidateMonomialExponent e i) =
      candidateMonomialDegree e i := by
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← candidateMonomialExponent_cast he i j]
  rfl

theorem candidateMonomial_homogeneous {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (i : Fin 3) :
    MvPolynomial.IsWeightedHomogeneous (xDegree (candidateSignature e)) (candidateMonomial e i)
      (candidateNatWeights e i • τ) := by
  apply MvPolynomial.isWeightedHomogeneous_monomial
  rw [candidateMonomialExponent_degree he i, candidate_monomial_degrees ha he τ hτ i]
  rw [← candidateNatWeights_cast he i]
  rfl


def candidateRootGenerator {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ)
    (i : Fin 3) : RootRing (candidateSignature e) τ :=
  ⟨ambientQuotient (candidateSignature e) (candidateMonomial e i), by
    apply (le_iSup (fun m : ℕ => ambientPiece (candidateSignature e) (m • τ)) (candidateNatWeights e i))
    exact Submodule.mem_map.mpr ⟨candidateMonomial e i, candidateMonomial_homogeneous ha he τ hτ i, rfl⟩⟩

theorem candidateRootGenerator_homogeneous {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (i : Fin 3) :
    candidateRootGenerator ha he τ hτ i ∈ rootPiece (candidateSignature e) τ (candidateNatWeights e i) :=
  Submodule.mem_map.mpr ⟨candidateMonomial e i, candidateMonomial_homogeneous ha he τ hτ i, rfl⟩

/-- A concrete polynomial algebra map into the actual root subalgebra.
Factoring through the Cox relation and proving bijectivity are separate steps. -/
def candidatePolynomialMap {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] RootRing (candidateSignature e) τ :=
  MvPolynomial.aeval (candidateRootGenerator ha he τ hτ)

@[simp] theorem candidatePolynomialMap_X {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (i : Fin 3) :
    candidatePolynomialMap ha he τ hτ (MvPolynomial.X i) = candidateRootGenerator ha he τ hτ i := by
  simp [candidatePolynomialMap]

end CanonicalRoots
