import CanonicalRoots.ChainNormalForm
import CanonicalRoots.ChainMonicSpan
import CanonicalRoots.ChainSurjection
import CanonicalRoots.CoxMonicRealization

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- The actual type-IV Cox map is injective, using the independent reduced monomials. -/
theorem candidateQuotientMap_injective_chain {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) :
    Function.Injective (candidateQuotientMap ha he τ hτ) := by
  let p := candidateSignature ⟨.IV,α,β,γ⟩
  let f := (rootSubalgebra p τ).val.toLinearMap.comp (candidateQuotientMap ha he τ hτ).toLinearMap
  let v := fun d : {d : Fin 3 →₀ ℕ // d 2 < γ} =>
    (Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation ⟨.IV,α,β,γ⟩})) (monomial d.val 1)
  have hv : Submodule.span ℂ (Set.range v) = ⊤ := candidateChainMonomials_span α β γ he.2.2.1
  have hfv : f ∘ v = fun d : {d : Fin 3 →₀ ℕ // d 2 < γ} =>
      ambientQuotient p (monomial (candidateExponentMap ⟨.IV,α,β,γ⟩ d.val) 1) := by
    funext d
    exact candidateQuotientMap_monomial_val ha he τ hτ d.val
  have hinj : Function.Injective f := LinearMap.injective_of_linearIndependent hv (by
    rw [hfv]
    exact chainReducedQuotient_linearIndependent he)
  intro x y h
  exact hinj (congrArg (fun r : RootRing p τ => (r : AmbientRing p)) h)

def candidateChainAlgEquiv {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) :
    PresentedRing (candidateRelation ⟨.IV,α,β,γ⟩) ≃ₐ[ℂ]
      RootRing (candidateSignature ⟨.IV,α,β,γ⟩) τ :=
  AlgEquiv.ofBijective (candidateQuotientMap ha he τ hτ)
    ⟨candidateQuotientMap_injective_chain ha he τ hτ,
      candidateQuotientMap_surjective_chain ha he τ hτ⟩

def candidateChainGradedEquiv {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) :
    GradedAlgEquiv (presentedPiece (candidateRelation ⟨.IV,α,β,γ⟩) (candidateNatWeights ⟨.IV,α,β,γ⟩))
      (rootPiece (candidateSignature ⟨.IV,α,β,γ⟩) τ) where
  toAlgEquiv := candidateChainAlgEquiv ha he τ hτ
  preserves := candidateQuotientMap_preserves_iff ha he τ hτ
    (candidateQuotientMap_injective_chain ha he τ hτ)

/-- The type-IV equation presents the actual isolated canonical-root ring, with its grading. -/
def chainCandidatePresentation {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩)
    (τ : DegreeGroup (candidateSignature ⟨.IV,α,β,γ⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.IV,α,β,γ⟩) a τ) :
    RootHypersurfacePresentation (candidateSignature ⟨.IV,α,β,γ⟩) τ where
  weights := candidateNatWeights ⟨.IV,α,β,γ⟩
  weights_pos := candidateNatWeights_pos he
  relationDegree := candidateNatDegree ⟨.IV,α,β,γ⟩
  relationDegree_pos := candidateNatDegree_pos he
  polynomial := candidateRelation ⟨.IV,α,β,γ⟩
  polynomial_ne_zero := candidateRelation_ne_zero _
  homogeneous := candidateRelation_homogeneous he
  no_constant_or_linear := candidateRelation_no_constant_or_linear ha he
  isolated := candidateRelation_isolated he
  graded_equiv := candidateChainGradedEquiv ha he τ hτ

theorem chain_candidate_realization {a α β γ : ℕ} (ha : 1 ≤ a)
    (he : ArithmeticTernary a ⟨.IV,α,β,γ⟩) :
    ∃ t : Target 3 a, t.signature = candidateSignature ⟨.IV,α,β,γ⟩ ∧
      (∀ i, (t.presentation.weights i : ℤ) = candidateWeights ⟨.IV,α,β,γ⟩ i) ∧
      (t.presentation.relationDegree : ℤ) = candidateDegree ⟨.IV,α,β,γ⟩ ∧
      t.presentation.polynomial = candidateRelation ⟨.IV,α,β,γ⟩ := by
  obtain ⟨τ,hτ,_⟩ := candidate_root_exists_unique ha he
  let t : Target 3 a := ⟨by decide, ha, candidateSignature ⟨.IV,α,β,γ⟩,
    candidateSignature_admissible ha he, τ, hτ, chainCandidatePresentation ha he τ hτ⟩
  exact ⟨t,rfl,candidateNatWeights_cast he,candidateNatDegree_cast he,rfl⟩

end CanonicalRoots
