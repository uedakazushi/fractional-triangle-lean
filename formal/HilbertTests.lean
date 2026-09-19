import CanonicalRoots.RootMonomialBasis

namespace CanonicalRoots.HilbertTests

/-- These compute dimensions of actual quotient subspaces, not enumerator outputs. -/
theorem fermat237_degree_one :
    Module.finrank ℂ (rootPiece ![2,3,7] (omegaDegree ![2,3,7]) 1) = 0 := by
  rw [omega_normalDegree, rootHilbert_formula _ (by decide +kernel)]
  norm_num [normalHilbertCoefficient, rootCarry, Fin.sum_univ_succ]

theorem fermat237_degree_six :
    Module.finrank ℂ (rootPiece ![2,3,7] (omegaDegree ![2,3,7]) 6) = 1 := by
  rw [omega_normalDegree, rootHilbert_formula _ (by decide +kernel)]
  norm_num [normalHilbertCoefficient, rootCarry, Fin.sum_univ_succ]

theorem fermat237_degree_fortytwo :
    Module.finrank ℂ (rootPiece ![2,3,7] (omegaDegree ![2,3,7]) 42) = 2 := by
  rw [omega_normalDegree, rootHilbert_formula _ (by decide +kernel)]
  norm_num [normalHilbertCoefficient, rootCarry, Fin.sum_univ_succ]

/-- This signature has a degree group with torsion; the calculation retains that group. -/
theorem fermat444_degree_three :
    Module.finrank ℂ (rootPiece ![4,4,4] (omegaDegree ![4,4,4]) 3) = 1 := by
  rw [omega_normalDegree, rootHilbert_formula _ (by decide +kernel)]
  norm_num [normalHilbertCoefficient, rootCarry, Fin.sum_univ_succ]

theorem fermat444_degree_four :
    Module.finrank ℂ (rootPiece ![4,4,4] (omegaDegree ![4,4,4]) 4) = 2 := by
  rw [omega_normalDegree, rootHilbert_formula _ (by decide +kernel)]
  norm_num [normalHilbertCoefficient, rootCarry, Fin.sum_univ_succ]

end CanonicalRoots.HilbertTests
