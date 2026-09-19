import CanonicalRoots.HypersurfaceMultiplicity

noncomputable section
namespace CanonicalRoots.NumericalTests

private theorem admissible444 : AdmissibleSignature ![4,4,4] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

/-- Eventual positivity does not mean every positive degree is nonzero. -/
example : Module.finrank ℂ (rootPiece ![4,4,4] (omegaDegree ![4,4,4]) 1) = 0 := by
  rw [omega_normalDegree, rootHilbert_formula _ (by decide +kernel)]
  norm_num [normalHilbertCoefficient, rootCarry, Fin.sum_univ_succ]

example : ∃ M : ℕ, ∀ m ≥ M,
    0 < Module.finrank ℂ (rootPiece ![4,4,4] (omegaDegree ![4,4,4]) m) :=
  rootPiece_eventually_finrank_pos (by decide) _ admissible444 (a := 1)
    (by decide) _ (by simp [IsCanonicalRoot])

/-- Torsion in the actual degree group is not discarded in the polynomial-degree comparison. -/
example : (rootBoxPolynomial ![4,4,4] (omegaDegree ![4,4,4]) 1).natDegree = 9 := by
  have hden := canonicalRoot_nat_denominator ![4,4,4] admissible444 (a := 1) (by decide)
    (omegaDegree ![4,4,4]) (by simp [IsCanonicalRoot])
  change signatureLcm ![4,4,4] • omegaDegree ![4,4,4] =
    canonicalRootScale ![4,4,4] 1 • cDegree ![4,4,4] at hden
  rw [show signatureLcm ![4,4,4] = 4 from by decide +kernel,
    show canonicalRootScale ![4,4,4] 1 = 1 from by decide +kernel] at hden
  exact rootBoxPolynomial_natDegree _ admissible444 (a := 1) (by decide) _
    (by simp [IsCanonicalRoot]) 4 1 (by decide) hden (by decide)

example (P : RootHypersurfacePresentation ![4,4,4] (omegaDegree ![4,4,4])) :
    Finset.univ.gcd P.weights = 1 :=
  P.weights_gcd_eq_one (by decide) _ admissible444 (a := 1) (by decide) _
    (by simp [IsCanonicalRoot])

example (P : RootHypersurfacePresentation ![4,4,4] (omegaDegree ![4,4,4])) :
    P.relationDegree = 1 + ∑ i, P.weights i :=
  P.relationDegree_eq_add_sum_weights _ admissible444 (a := 1) (by decide) _
    (by simp [IsCanonicalRoot])

private def squareRelation : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 ^ 2
private theorem square_homogeneous :
    MvPolynomial.IsWeightedHomogeneous (fun _ : Fin 2 => 1) squareRelation 2 := by
  have h := (MvPolynomial.isWeightedHomogeneous_X ℂ (fun _ : Fin 2 => 1) 0).pow 2
  rw [show 2 • (1 : ℕ) = 2 from rfl] at h
  exact h
private theorem square_ne_zero : squareRelation ≠ 0 := by
  exact pow_ne_zero _ (MvPolynomial.X_ne_zero 0)

/-- The Hilbert calculation applies to a nonreduced quotient too: no hidden domain hypothesis. -/
private theorem square_hilbert :
    presentedHilbertSeries squareRelation (fun _ : Fin 2 => 1) =
      (1 - PowerSeries.X ^ 2) * (PowerSeries.invOneSubPow ℚ 2).val := by
  rw [presentedHilbertSeries_eq _ _ (by decide) 2 square_homogeneous square_ne_zero,
    weightedPolynomialHilbertSeries_eq_geometric _ (by decide)]
  congr 1
  simp only [weightedGeometricSeries, PowerSeries.expand_one_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℕ) = 1 + 1 from rfl, PowerSeries.invOneSubPow_add, Units.val_mul]
  ring

example : Module.finrank ℂ (presentedPiece squareRelation (fun _ : Fin 2 => 1) 0) = 1 := by
  have he := congrArg PowerSeries.constantCoeff square_hilbert
  norm_num [presentedHilbertSeries, PowerSeries.invOneSubPow] at he
  exact_mod_cast he

example : Module.finrank ℂ (presentedPiece squareRelation (fun _ : Fin 2 => 1) 1) = 2 := by
  have he := congrArg (PowerSeries.coeff 1) square_hilbert
  norm_num [presentedHilbertSeries, sub_mul, PowerSeries.coeff_X_pow_mul',
    invOneSubPow_coeff] at he
  exact_mod_cast he

example : Module.finrank ℂ (presentedPiece squareRelation (fun _ : Fin 2 => 1) 2) = 2 := by
  have he := congrArg (PowerSeries.coeff 2) square_hilbert
  norm_num [presentedHilbertSeries, sub_mul, PowerSeries.coeff_X_pow_mul',
    invOneSubPow_coeff] at he
  exact_mod_cast he

end CanonicalRoots.NumericalTests

#check CanonicalRoots.rootPiece_eventually_finrank_pos
#check CanonicalRoots.RootHypersurfacePresentation.weights_gcd_eq_one
#check CanonicalRoots.presentedPiece_finrank_add
#check CanonicalRoots.presentedHilbertSeries_mul_denominator
#check CanonicalRoots.rootBoxPolynomial_natDegree
#check CanonicalRoots.RootHypersurfacePresentation.relationDegree_eq_add_sum_weights
#check CanonicalRoots.RootHypersurfacePresentation.box_card_mul_weights
#check CanonicalRoots.Target.relationDegree_eq_add_sum_weights
#check CanonicalRoots.Target.weights_gcd_eq_one
