import CanonicalRoots.TernaryInvertibleSupport
import CanonicalRoots.DiagonalPolynomialEquiv
import CanonicalRoots.TernaryRealization

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem InvertiblePolynomial.ternary_principal_candidate {a h : ℕ}
    {f : MvPolynomial (Fin 3) ℂ} {w : Fin 3 → ℕ} (F : InvertiblePolynomial f w h)
    (ha : 1 ≤ a) (hprincipal : F.IsPrincipal) (hdef : h = a + ∑ i, w i) :
    ∃ σ ρ : Equiv.Perm (Fin 3), ∃ e : TernaryCandidate,
      ArithmeticTernary a e ∧ candidateNatWeights e = w ∘ σ ∧ candidateNatDegree e = h ∧
      (∀ i j, (F.exponent (ρ i) (σ j) : ℤ) =
        Cox.exponents e.kind e.alpha e.beta e.gamma i j) := by
  obtain ⟨σ,ρ,e,hα,hβ,hγ,hE⟩ := F.ternary_cox_matrix (by omega)
  have hmat : F.exponentMatrix.submatrix ρ σ = Cox.exponents e.kind e.alpha e.beta e.gamma :=
    funext (fun i => funext (hE i))
  have hdegpos : 0 < candidateDegree e := Cox.degree_pos e.kind e.alpha e.beta e.gamma
    (by exact_mod_cast hα) (by exact_mod_cast hβ) (by exact_mod_cast hγ)
  have hd : candidateDegree e = (h : ℤ) := by
    have hh := Matrix.abs_det_submatrix_equiv_equiv ρ σ F.exponentMatrix
    rw [hmat, Cox.determinant] at hh
    change |candidateDegree e| = |F.exponentMatrix.det| at hh
    rw [abs_of_pos hdegpos] at hh
    exact hh.trans hprincipal.2
  have hhom (i : Fin 3) :
      ∑ j, Cox.exponents e.kind e.alpha e.beta e.gamma i j * (w (σ j) : ℤ) = h := by
    simp_rw [← hE]
    rw [Equiv.sum_comp σ (fun j => (F.exponent (ρ i) j : ℤ) * (w j : ℤ))]
    exact F.degree_equations (ρ i)
  have hw (i : Fin 3) : candidateWeights e i = (w (σ i) : ℤ) := by
    have he := Cox.weight_proportional e.kind e.alpha e.beta e.gamma h
      (fun j => (w (σ j) : ℤ)) (ne_of_gt hdegpos) hhom i
    change candidateDegree e * (w (σ i) : ℤ) = (h : ℤ) * candidateWeights e i at he
    rw [hd] at he
    exact (mul_left_cancel₀ (by exact_mod_cast ne_of_gt F.degree_pos) he).symm
  have he : ArithmeticTernary a e := by
    refine ⟨hα,hβ,hγ,?_,?_⟩
    · rw [hw 0, hw 1, hw 2]
      simp only [Int.gcd_natCast_natCast, ← Nat.gcd_assoc]
      exact primitive_ternary_gcd_perm w hprincipal.1 σ
    · change candidateDegree e - ∑ i, candidateWeights e i = a
      simp_rw [hd, hw]
      rw [Equiv.sum_comp σ (fun i => (w i : ℤ))]
      have he : (h : ℤ) = (a : ℤ) + ∑ i, (w i : ℤ) := by exact_mod_cast hdef
      linarith
  refine ⟨σ,ρ,e,he,?_,?_,hE⟩
  · funext i
    apply Int.ofNat_injective
    exact (candidateNatWeights_cast he i).trans (hw i)
  · apply Int.ofNat_injective
    exact (candidateNatDegree_cast he).trans hd

theorem InvertiblePolynomial.normalize_coefficients {n h : ℕ}
    {f : MvPolynomial (Fin n) ℂ} {w : Fin n → ℕ} (F : InvertiblePolynomial f w h) :
    ∃ s : Fin n → ℂ, (∀ i, s i ≠ 0) ∧
      diagonalPolynomialMap s f = ∑ i, monomial (F.exponent i) 1 := by
  obtain ⟨s,hs,hprod⟩ := exponent_torus_surjective (fun i j => F.exponent i j)
    F.determinant_ne_zero (fun i => (F.coefficient i)⁻¹)
    (fun i => inv_ne_zero (F.coefficient_ne_zero i))
  refine ⟨s,hs,?_⟩
  calc
    _ = diagonalPolynomialMap s (∑ i, monomial (F.exponent i) (F.coefficient i)) :=
      congrArg (diagonalPolynomialMap s) F.polynomial_eq
    _ = _ := by
      rw [map_sum]
      simp only [diagonalPolynomialMap_monomial, hprod, mul_inv_cancel₀ (F.coefficient_ne_zero _)]

/-- Every input ternary invertible polynomial satisfying (1.6), including its
arbitrary nonzero coefficients, is the presentation of an actual canonical root.
The arithmetic candidate and both coordinate changes are derived in the proof. -/
theorem principal_ternary_invertible_realization {a h : ℕ}
    {f : MvPolynomial (Fin 3) ℂ} {w : Fin 3 → ℕ} (F : InvertiblePolynomial f w h)
    (ha : 1 ≤ a) (hprincipal : F.IsPrincipal) (hdef : h = a + ∑ i, w i) :
    ∃ t : Target 3 a, t.presentation.polynomial = f ∧
      t.presentation.weights = w ∧ t.presentation.relationDegree = h := by
  obtain ⟨σ,ρ,e,he,hw,hd,hE⟩ := F.ternary_principal_candidate ha hprincipal hdef
  obtain ⟨s,hs,hf⟩ := F.normalize_coefficients
  have hpoly : rename σ.symm (diagonalPolynomialMap s f) = candidateRelation e := by
    rw [hf, map_sum]
    rw [← Equiv.sum_comp ρ (fun i => rename σ.symm (monomial (F.exponent i) (1 : ℂ)))]
    unfold candidateRelation
    apply Finset.sum_congr rfl
    intro i _
    rw [rename_monomial]
    apply congrArg (fun d : Fin 3 →₀ ℕ => monomial d (1 : ℂ))
    ext j
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm]
    apply Int.ofNat_injective
    exact (hE i j).trans (candidateRelationExponent_cast he i j).symm
  have φ := (presentedGradedDiagonal s hs f w).trans
    (presentedGradedRename (diagonalPolynomialMap s f) w σ.symm)
  change GradedAlgEquiv (presentedPiece f w)
    (presentedPiece (rename σ.symm (diagonalPolynomialMap s f)) (w ∘ σ)) at φ
  rw [hpoly, ← hw] at φ
  let t := candidateTarget ha he
  let H : RootHypersurfacePresentation t.signature t.tau := {
    weights := w
    weights_pos := F.weights_pos
    relationDegree := h
    relationDegree_pos := F.degree_pos
    polynomial := f
    polynomial_ne_zero := by
      intro hz
      have hc := F.coeff_exponent 0
      simp only [hz] at hc
      exact F.coefficient_ne_zero 0 hc.symm
    homogeneous := F.homogeneous
    no_constant_or_linear := F.no_constant_or_linear
    isolated := F.isolated
    graded_equiv := φ.trans (candidateTargetGradedEquiv ha he) }
  exact ⟨{t with presentation := H},rfl,rfl,rfl⟩

end CanonicalRoots
