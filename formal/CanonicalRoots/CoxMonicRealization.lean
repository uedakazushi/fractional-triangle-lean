import CanonicalRoots.CoxCandidateGrading
import CanonicalRoots.CoxCandidateIsolated

noncomputable section
namespace CanonicalRoots

/-- All presentation fields, including isolation and the actual graded isomorphism, for II and III. -/
def monicCandidatePresentation {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    RootHypersurfacePresentation (candidateSignature e) τ where
  weights := candidateNatWeights e
  weights_pos := candidateNatWeights_pos he
  relationDegree := candidateNatDegree e
  relationDegree_pos := candidateNatDegree_pos he
  polynomial := candidateRelation e
  polynomial_ne_zero := candidateRelation_ne_zero e
  homogeneous := candidateRelation_homogeneous he
  no_constant_or_linear := candidateRelation_no_constant_or_linear ha he
  isolated := candidateRelation_isolated he
  graded_equiv := candidateMonicGradedEquiv ha he hk τ hτ

theorem monic_candidate_realization {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III) :
    ∃ t : Target 3 a, t.signature = candidateSignature e ∧
      (∀ i, (t.presentation.weights i : ℤ) = candidateWeights e i) ∧
      (t.presentation.relationDegree : ℤ) = candidateDegree e ∧
      t.presentation.polynomial = candidateRelation e := by
  obtain ⟨τ,hτ,_⟩ := candidate_root_exists_unique ha he
  let t : Target 3 a := ⟨by decide, ha, candidateSignature e, candidateSignature_admissible ha he,
    τ, hτ, monicCandidatePresentation ha he hk τ hτ⟩
  exact ⟨t,rfl,candidateNatWeights_cast he,candidateNatDegree_cast he,rfl⟩

end CanonicalRoots
