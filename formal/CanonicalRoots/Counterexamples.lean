import CanonicalRoots.Semantics

noncomputable section
namespace CanonicalRoots.Counterexamples
open MvPolynomial

def branched : MvPolynomial (Fin 3) ℂ :=
  X 0 ^ 3 * X 1 + X 1 * X 2 ^ 3 + X 1 ^ 4

theorem branched_has_nonzero_critical_point :
    ∀ i : Fin 3, eval ![1,0,-1] (pderiv i branched) = 0 := by
  intro i
  fin_cases i <;> norm_num [branched, pderiv_mul, pderiv_pow, Pi.single_apply]

theorem branched_not_isolated : ¬ IsolatedAtOrigin branched := by
  intro h
  have hz := (h ![1,0,-1]).mp branched_has_nonzero_critical_point
  have := congrFun hz 0
  norm_num at this

theorem branched_determinant_nonzero :
    (Matrix.det (!![(3 : ℤ),1,0; 0,1,3; 0,4,0])) = -36 := by
  norm_num [Matrix.det_fin_three]

/-- The determinant of this presentation differs from its primitive degree. -/
theorem nonprincipal_fermat_determinant :
    (Matrix.det (!![(2 : ℤ),0,0; 0,3,0; 0,0,8])) = 48 := by
  norm_num [Matrix.det_fin_three]

theorem nonprincipal_fermat_weights :
    (2 : ℤ)*12=24 ∧ (3 : ℤ)*8=24 ∧ (8 : ℤ)*3=24 ∧
    24-(12+8+3 : ℤ)=1 ∧ (48 : ℤ)≠24 := by norm_num

/-- This parameter passes root arithmetic; the non-hypersurface claim is still not formalized. -/
theorem nonmaximal_root_numbers :
    (2*3*7*67 : ℤ) - (3*7*67+2*7*67+2*3*67+2*3*7)=25 ∧
    (5 : ℤ) ∣ 25 ∧ Nat.Coprime 5 (2*3*7*67) := by norm_num

end CanonicalRoots.Counterexamples
