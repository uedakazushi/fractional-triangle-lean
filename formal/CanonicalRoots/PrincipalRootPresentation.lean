import CanonicalRoots.InvertiblePolynomial
import CanonicalRoots.TernaryRealization
import CanonicalRoots.HigherConverse

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def candidateInvertiblePolynomial {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) :
    InvertiblePolynomial (candidateRelation e) (candidateNatWeights e) (candidateNatDegree e) where
  exponent := candidateRelationExponent e
  coefficient := fun _ => 1
  coefficient_ne_zero := fun _ => one_ne_zero
  polynomial_eq := rfl
  determinant_ne_zero := by
    have hm : (fun i j => (candidateRelationExponent e i j : ℤ)) =
        Cox.exponents e.kind e.alpha e.beta e.gamma := funext (fun i => funext (candidateRelationExponent_cast he i))
    rw [hm, Cox.determinant]
    exact ne_of_gt (Cox.degree_pos e.kind e.alpha e.beta e.gamma
      (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1))
  weights_pos := candidateNatWeights_pos he
  degree_pos := candidateNatDegree_pos he
  homogeneous := candidateRelation_homogeneous he
  no_constant_or_linear := candidateRelation_no_constant_or_linear ha he
  isolated := candidateRelation_isolated he

theorem candidateInvertiblePolynomial_principal {a : ℕ} (ha : 1 ≤ a)
    {e : TernaryCandidate} (he : ArithmeticTernary a e) :
    (candidateInvertiblePolynomial ha he).IsPrincipal := by
  constructor
  · rw [← candidateTarget_weights ha he]
    exact (candidateTarget ha he).weights_gcd_eq_one
  · have hm : (candidateInvertiblePolynomial ha he).exponentMatrix =
        Cox.exponents e.kind e.alpha e.beta e.gamma :=
      funext (fun i => funext (candidateRelationExponent_cast he i))
    rw [hm, Cox.determinant, candidateNatDegree_cast he]
    exact abs_of_pos (Cox.degree_pos e.kind e.alpha e.beta e.gamma
      (by exact_mod_cast he.1) (by exact_mod_cast he.2.1) (by exact_mod_cast he.2.2.1))

def fermatInvertiblePolynomial {n : ℕ} (_hn : 0 < n) (p : Fin n → ℕ)
    (hp : ∀ i, 2 ≤ p i) :
    InvertiblePolynomial (fermat p) (productWeights p) (∏ i, p i) where
  exponent i := Finsupp.single i (p i)
  coefficient := fun _ => 1
  coefficient_ne_zero := fun _ => one_ne_zero
  polynomial_eq := by simp only [fermat, X_pow_eq_monomial]
  determinant_ne_zero := by
    have hm : (fun i j => ((Finsupp.single i (p i) : Fin n →₀ ℕ) j : ℤ)) =
        Matrix.diagonal (fun i => (p i : ℤ)) := by
      ext i j
      simp only [Finsupp.single_apply, Matrix.diagonal_apply]
      split_ifs with hij
      · subst j; rfl
      · rfl
    rw [hm, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by have := hp i; exact_mod_cast (by omega : p i ≠ 0))
  weights_pos := productWeights_pos p (fun i => by have := hp i; omega)
  degree_pos := Finset.prod_pos (fun i _ => by have := hp i; omega)
  homogeneous := fermat_product_homogeneous p
  no_constant_or_linear := fermat_no_constant_or_linear p hp
  isolated := fermat_isolated p hp

theorem fermatInvertiblePolynomial_determinant {n : ℕ} (hn : 0 < n) (p : Fin n → ℕ)
    (hp : ∀ i, 2 ≤ p i) :
    (fermatInvertiblePolynomial hn p hp).exponentMatrix.det = (∏ i, p i : ℕ) := by
  have hm : (fermatInvertiblePolynomial hn p hp).exponentMatrix =
      Matrix.diagonal (fun i => (p i : ℤ)) := by
    ext i j
    simp [InvertiblePolynomial.exponentMatrix, fermatInvertiblePolynomial,
      Finsupp.single_apply, Matrix.diagonal_apply]
  rw [hm, Matrix.det_diagonal, Nat.cast_prod]

/-- Forward direction of manuscript Theorem 1.4 in every dimension.
The root ring receives a new, actually graded-isomorphic, principal invertible
presentation. No determinant condition is imposed on the original equation. -/
theorem canonical_root_invertible_presentation {n a : ℕ} (t : Target n a) :
    ∃ H : RootHypersurfacePresentation t.signature t.tau,
      ∃ F : InvertiblePolynomial H.polynomial H.weights H.relationDegree,
        F.IsPrincipal ∧ H.relationDegree = a + ∑ i, H.weights i := by
  by_cases hn : n = 3
  · subst n
    obtain ⟨e,he,⟨φ⟩⟩ := t.ternary_candidate_model
    let F := candidateInvertiblePolynomial t.parameter_input he
    let H : RootHypersurfacePresentation t.signature t.tau := {
      weights := candidateNatWeights e
      weights_pos := F.weights_pos
      relationDegree := candidateNatDegree e
      relationDegree_pos := F.degree_pos
      polynomial := candidateRelation e
      polynomial_ne_zero := candidateRelation_ne_zero e
      homogeneous := F.homogeneous
      no_constant_or_linear := F.no_constant_or_linear
      isolated := F.isolated
      graded_equiv := φ.symm }
    exact ⟨H,F,candidateInvertiblePolynomial_principal t.parameter_input he,
      candidateNatDegree_eq_add_sum_weights he⟩
  · cases n with
    | zero => have := t.dimension_input; omega
    | succ n =>
      have hn3 : 3 ≤ n := by have := t.dimension_input; omega
      have hc := t.pairwise_coprime hn3
      have hd := t.higher_product_defect hn3
      let H := higherRootPresentation (by omega) t.signature t.admissible.1
        t.parameter_input hc hd t.tau t.root_equation
      let F := fermatInvertiblePolynomial (by omega) t.signature t.admissible.1
      have hg : Finset.univ.gcd (productWeights t.signature) = 1 :=
        (show Target (n + 1) a from {t with presentation := H}).weights_gcd_eq_one
      refine ⟨H,F,⟨hg,?_⟩,?_⟩
      · change |(fermatInvertiblePolynomial _ _ _).exponentMatrix.det| = _
        rw [fermatInvertiblePolynomial_determinant]
        exact abs_of_nonneg (by positivity)
      · change (∏ i, t.signature i) = a + ∑ i, productWeights t.signature i
        have he : ((∏ i, t.signature i : ℕ) : ℤ) =
            (a : ℤ) + ∑ i, (productWeights t.signature i : ℤ) := by linarith
        exact_mod_cast he

/-- A higher-dimensional isolated root has the largest possible positive root index.
In fact every other positive root index divides it. -/
theorem Target.higher_root_index_maximal {n a : ℕ} (t : Target (n + 1) a)
    (hn : 3 ≤ n) {d : ℕ} (_hd : 1 ≤ d) (υ : DegreeGroup t.signature)
    (hυ : IsCanonicalRoot t.signature d υ) : d ∣ a ∧ d ≤ a := by
  have hp : ∀ i, 0 < t.signature i := fun i => by have := t.admissible.1 i; omega
  have hindex : signatureIndex t.signature = (a : ℤ) := by
    rw [signatureIndex_eq_productDegree t.signature t.admissible (t.pairwise_coprime hn),
      productDegree_omega]
    simpa only [Nat.cast_prod] using t.higher_product_defect hn
  have he := (canonicalRoot_exists_iff t.signature hp).mp ⟨υ,hυ⟩
  have hdiv : d ∣ a := by
    have hi : (d : ℤ) ∣ (a : ℤ) := hindex ▸ he.1
    exact_mod_cast hi
  exact ⟨hdiv,Nat.le_of_dvd (by have := t.parameter_input; omega) hdiv⟩

end CanonicalRoots
