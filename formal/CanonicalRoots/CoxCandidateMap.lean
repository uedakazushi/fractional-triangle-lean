import CanonicalRoots.CoxCandidateRelation

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- The polynomial map has exactly the prescribed monomial images in the ambient quotient. -/
theorem candidatePolynomialMap_val {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    (rootSubalgebra (candidateSignature e) τ).val.comp (candidatePolynomialMap ha he τ hτ) =
      (ambientQuotient (candidateSignature e)).comp (aeval (candidateMonomial e)) := by
  ext i
  simp [candidatePolynomialMap, candidateRootGenerator]

theorem candidatePolynomialMap_relation {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    candidatePolynomialMap ha he τ hτ (candidateRelation e) = 0 := by
  have hf : ambientQuotient (candidateSignature e) (fermat (candidateSignature e)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply Subtype.ext
  change ((rootSubalgebra (candidateSignature e) τ).val.comp
    (candidatePolynomialMap ha he τ hτ)) (candidateRelation e) = 0
  rw [candidatePolynomialMap_val]
  change ambientQuotient (candidateSignature e) (aeval (candidateMonomial e) (candidateRelation e)) = 0
  rw [candidate_relation_substitution he, map_mul, hf, mul_zero]

/-- The actual Cox quotient maps into its actual canonical-root subalgebra.
No injectivity or surjectivity is built into this definition. -/
def candidateQuotientMap {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate} (he : ArithmeticTernary a e)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    PresentedRing (candidateRelation e) →ₐ[ℂ] RootRing (candidateSignature e) τ :=
  Ideal.Quotient.liftₐ (Ideal.span {candidateRelation e}) (candidatePolynomialMap ha he τ hτ) (by
    change Ideal.span {candidateRelation e} ≤ RingHom.ker (candidatePolynomialMap ha he τ hτ).toRingHom
    rw [Ideal.span_singleton_le_iff_mem]
    exact candidatePolynomialMap_relation ha he τ hτ)

@[simp] theorem candidateQuotientMap_mk {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (f : MvPolynomial (Fin 3) ℂ) :
    candidateQuotientMap ha he τ hτ ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) f) =
      candidatePolynomialMap ha he τ hτ f := rfl

end CanonicalRoots
