import CanonicalRoots.RootHilbertRational

noncomputable section
namespace CanonicalRoots.FiniteFreeTests

private theorem admissible444 : AdmissibleSignature ![4,4,4] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

/-- An actual torsion-containing degree group is retained in the finite-free theorem. -/
example : Module.Free
    (canonicalPowerSubalgebra ![4,4,4] admissible444 (a := 1) (by decide)
      (omegaDegree ![4,4,4]) (by simp [IsCanonicalRoot]))
    (RootRing ![4,4,4] (omegaDegree ![4,4,4])) :=
  canonicalRoot_free _ admissible444 (by decide) _ (by simp [IsCanonicalRoot])

example : IsNoetherianRing (RootRing ![4,4,4] (omegaDegree ![4,4,4])) :=
  canonicalRoot_noetherian _ admissible444 (a := 1) (by decide) _ (by simp [IsCanonicalRoot])

private theorem admissible23767 : AdmissibleSignature ![2,3,7,67] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

/-- This example has scale u=25, so the construction is not restricted to the u=1 family. -/
example : canonicalRootScale ![2,3,7,67] 1 = 25 := by decide +kernel

example : Module.Finite
    (canonicalPowerSubalgebra ![2,3,7,67] admissible23767 (a := 1) (by decide)
      (omegaDegree ![2,3,7,67]) (by simp [IsCanonicalRoot]))
    (RootRing ![2,3,7,67] (omegaDegree ![2,3,7,67])) :=
  canonicalRoot_finite _ admissible23767 (by decide) _ (by simp [IsCanonicalRoot])

/-- Boundary cases in the composition formula include zero variables and absent degrees. -/
example : weightedCompositionCount 0 7 3 3 = 1 := by decide +kernel
example : weightedCompositionCount 0 7 3 10 = 0 := by decide +kernel
example : weightedCompositionCount 2 7 3 2 = 0 := by decide +kernel
example : weightedCompositionCount 2 7 3 11 = 0 := by decide +kernel
example : weightedCompositionCount 2 7 3 17 = 3 := by decide +kernel

example : rootHilbertSeries ![4,4,4] (omegaDegree ![4,4,4]) *
    (1 - PowerSeries.X ^ 4) ^ 2 =
      rootBoxNumerator ![4,4,4] (omegaDegree ![4,4,4]) 1 := by
  simpa only [show signatureLcm ![4,4,4] = 4 from by decide +kernel,
      show canonicalRootScale ![4,4,4] 1 = 1 from by decide +kernel] using
    canonicalRootHilbertSeries_mul_denominator ![4,4,4] admissible444 (a := 1)
      (by decide) (omegaDegree ![4,4,4]) (by simp [IsCanonicalRoot])

end CanonicalRoots.FiniteFreeTests

#check CanonicalRoots.rootPowerGenerator_algebraicIndependent
#check CanonicalRoots.canonicalRootFiniteFreeBasis
#check CanonicalRoots.canonicalRoot_finiteType
#check CanonicalRoots.canonicalRoot_noetherian
#check CanonicalRoots.rootPiece_finrank_box_sum
#check CanonicalRoots.canonicalRootHilbertSeries_mul_denominator
#check CanonicalRoots.rootHilbertSeries_eq_rational
#check CanonicalRoots.rootHilbertRationalValue_reciprocal

#check CanonicalRoots.canonicalRootHilbertSeries_eq_rational
#check CanonicalRoots.canonicalRootHilbertRational_reciprocal
