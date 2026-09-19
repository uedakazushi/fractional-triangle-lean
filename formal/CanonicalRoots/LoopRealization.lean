import CanonicalRoots.LoopPolynomialDomain
import CanonicalRoots.LoopSurjection
import CanonicalRoots.HypersurfaceDimensionInjection
import CanonicalRoots.CoxMonicRealization

noncomputable section
namespace CanonicalRoots

/-- Surjectivity and the domain dimension bound make the actual loop Cox map injective. -/
theorem candidateQuotientMap_injective_loop {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) :
    Function.Injective (candidateQuotientMap ha he τ hτ) := by
  haveI := loopPresentedRing_isDomain α β γ (Nat.le_trans (by decide) he.2.1) he.2.2.1
  exact hypersurface_surjection_injective _ (candidateSignature_admissible ha he) ha τ hτ _
    (candidateRelation_ne_zero _) (candidateQuotientMap ha he τ hτ)
    (candidateQuotientMap_surjective_loop ha he τ hτ)

def candidateLoopAlgEquiv {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) :
    PresentedRing (candidateRelation ⟨.V,α,β,γ⟩) ≃ₐ[ℂ]
      RootRing (candidateSignature ⟨.V,α,β,γ⟩) τ :=
  AlgEquiv.ofBijective (candidateQuotientMap ha he τ hτ)
    ⟨candidateQuotientMap_injective_loop ha he τ hτ,
      candidateQuotientMap_surjective_loop ha he τ hτ⟩

def candidateLoopGradedEquiv {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) :
    GradedAlgEquiv (presentedPiece (candidateRelation ⟨.V,α,β,γ⟩) (candidateNatWeights ⟨.V,α,β,γ⟩))
      (rootPiece (candidateSignature ⟨.V,α,β,γ⟩) τ) where
  toAlgEquiv := candidateLoopAlgEquiv ha he τ hτ
  preserves := candidateQuotientMap_preserves_iff ha he τ hτ
    (candidateQuotientMap_injective_loop ha he τ hτ)

/-- Type V is an isolated graded presentation of the actual canonical-root subring. -/
def loopCandidatePresentation {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.V,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,α,β,γ⟩) a τ) :
    RootHypersurfacePresentation (candidateSignature ⟨.V,α,β,γ⟩) τ where
  weights := candidateNatWeights ⟨.V,α,β,γ⟩
  weights_pos := candidateNatWeights_pos he
  relationDegree := candidateNatDegree ⟨.V,α,β,γ⟩
  relationDegree_pos := candidateNatDegree_pos he
  polynomial := candidateRelation ⟨.V,α,β,γ⟩
  polynomial_ne_zero := candidateRelation_ne_zero _
  homogeneous := candidateRelation_homogeneous he
  no_constant_or_linear := candidateRelation_no_constant_or_linear ha he
  isolated := candidateRelation_isolated he
  graded_equiv := candidateLoopGradedEquiv ha he τ hτ

theorem loop_candidate_realization {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.V,α,β,γ⟩) :
    ∃ t : Target 3 a, t.signature = candidateSignature ⟨.V,α,β,γ⟩ ∧
      (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.V,α,β,γ⟩ i) ∧
      (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.V,α,β,γ⟩ ∧
      t.presentation.polynomial = candidateRelation ⟨.V,α,β,γ⟩ := by
  obtain ⟨τ,hτ,_⟩ := candidate_root_exists_unique ha he
  let t : Target 3 a := ⟨by decide, ha, candidateSignature ⟨.V,α,β,γ⟩,
    candidateSignature_admissible ha he, τ, hτ, loopCandidatePresentation ha he τ hτ⟩
  exact ⟨t,rfl,candidateNatWeights_cast he,candidateNatDegree_cast he,rfl⟩

end CanonicalRoots
