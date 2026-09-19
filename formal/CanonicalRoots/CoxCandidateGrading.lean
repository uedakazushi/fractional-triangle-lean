import CanonicalRoots.CoxMonicSurjection
import CanonicalRoots.CoxCandidateHomogeneous

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem candidateExponentMap_degree {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight (xDegree (candidateSignature e)) (candidateExponentMap e d) =
      Finsupp.weight (candidateNatWeights e) d • τ := by
  simp only [candidateExponentMap, map_sum, map_nsmul, candidateMonomialExponent_degree he,
    candidate_monomial_degrees ha he τ hτ]
  simp_rw [← candidateNatWeights_cast he, natCast_zsmul, ← mul_nsmul]
  rw [Finsupp.weight_eq_sum, Finset.sum_smul]
  simp [smul_eq_mul, Nat.mul_comm]

theorem candidatePolynomialMap_monomial_homogeneous {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (d : Fin 3 →₀ ℕ) (c : ℂ) :
    candidatePolynomialMap ha he τ hτ (monomial d c) ∈
      rootPiece (candidateSignature e) τ (Finsupp.weight (candidateNatWeights e) d) := by
  have hc : monomial d c = c • (monomial d 1 : MvPolynomial (Fin 3) ℂ) := by
    simp [smul_monomial]
  rw [hc, map_smul]
  apply Submodule.smul_mem
  change (candidatePolynomialMap ha he τ hτ (monomial d 1) : AmbientRing (candidateSignature e)) ∈
    ambientPiece (candidateSignature e) (Finsupp.weight (candidateNatWeights e) d • τ)
  have hm := candidateQuotientMap_monomial_val ha he τ hτ d
  rw [candidateQuotientMap_mk] at hm
  rw [hm]
  exact Submodule.mem_map.mpr ⟨_, isWeightedHomogeneous_monomial _ _ _
    (candidateExponentMap_degree ha he τ hτ d), rfl⟩

theorem candidatePolynomialMap_homogeneous {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) {f : MvPolynomial (Fin 3) ℂ} {m : ℕ}
    (hf : IsWeightedHomogeneous (candidateNatWeights e) f m) :
    candidatePolynomialMap ha he τ hτ f ∈ rootPiece (candidateSignature e) τ m := by
  classical
  rw [← support_sum_monomial_coeff f, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have h := candidatePolynomialMap_monomial_homogeneous ha he τ hτ d (f.coeff d)
  rwa [hf (mem_support_iff.mp hd)] at h

theorem candidatePolynomialMap_projection {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (m : ℕ) (f : MvPolynomial (Fin 3) ℂ) :
    candidatePolynomialMap ha he τ hτ (weightedHomogeneousComponent (candidateNatWeights e) m f) =
      rootProjection (candidateSignature e) τ m (candidatePolynomialMap ha he τ hτ f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial d c =>
    rw [rootProjection_of_mem _ _ (root_multiples_injective _ (candidateSignature_admissible ha he) ha τ hτ)
      m _ (candidatePolynomialMap_monomial_homogeneous ha he τ hτ d c)]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ d c rfl)]
    split_ifs <;> simp

theorem candidateQuotientMap_preserves_iff {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ)
    (hinj : Function.Injective (candidateQuotientMap ha he τ hτ))
    (m : ℕ) (x : PresentedRing (candidateRelation e)) :
    x ∈ presentedPiece (candidateRelation e) (candidateNatWeights e) m ↔
      candidateQuotientMap ha he τ hτ x ∈ rootPiece (candidateSignature e) τ m := by
  constructor
  · rintro ⟨f,hf,rfl⟩
    change candidatePolynomialMap ha he τ hτ f ∈ rootPiece (candidateSignature e) τ m
    exact candidatePolynomialMap_homogeneous ha he τ hτ hf
  · intro hx
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {candidateRelation e}) x
    refine Submodule.mem_map.mpr ⟨weightedHomogeneousComponent (candidateNatWeights e) m f,
      weightedHomogeneousComponent_mem _ _ _, ?_⟩
    apply hinj
    change candidatePolynomialMap ha he τ hτ
      (weightedHomogeneousComponent (candidateNatWeights e) m f) = candidatePolynomialMap ha he τ hτ f
    rw [candidatePolynomialMap_projection]
    change candidatePolynomialMap ha he τ hτ f ∈ rootPiece (candidateSignature e) τ m at hx
    simpa using rootProjection_of_mem _ _
      (root_multiples_injective _ (candidateSignature_admissible ha he) ha τ hτ) m m hx

/-- Types II and III are realized with the original natural root grading. -/
def candidateMonicGradedEquiv {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    GradedAlgEquiv (presentedPiece (candidateRelation e) (candidateNatWeights e))
      (rootPiece (candidateSignature e) τ) where
  toAlgEquiv := candidateMonicAlgEquiv ha he hk τ hτ
  preserves := candidateQuotientMap_preserves_iff ha he τ hτ
    (candidateQuotientMap_injective_of_monic ha he hk τ hτ)

end CanonicalRoots
