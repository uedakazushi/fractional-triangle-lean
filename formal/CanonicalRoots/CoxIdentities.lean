import Mathlib
import CanonicalRoots.CoxData

namespace CanonicalRoots.Cox
open Matrix

theorem homogeneous (k : Kind) (a b c : ℤ) (i : Fin 3) :
    ∑ j, exponents k a b c i j * weights k a b c j = degree k a b c := by
  cases k <;> fin_cases i <;> simp [exponents, weights, degree, Fin.sum_univ_succ] <;> ring

theorem certificate_row_sum (k : Kind) (a b c : ℤ) (i : Fin 3) :
    ∑ j, certificate k a b c i j = weights k a b c i := by
  cases k <;> fin_cases i <;> simp [certificate, weights, Fin.sum_univ_succ] <;> ring

theorem integral_degree (k : Kind) (a b c : ℤ) (i j : Fin 3) :
    signature k a b c j * certificate k a b c i j =
      defect k a b c * monomials k a b c i j + weights k a b c i := by
  cases k <;> fin_cases i <;> fin_cases j <;>
    simp [signature, certificate, defect, degree, weights, monomials, Fin.sum_univ_succ] <;> ring

theorem substitution (k : Kind) (a b c : ℤ) (i j : Fin 3) :
    ∑ l, exponents k a b c i l * monomials k a b c l j =
      (if i = j then signature k a b c i else 0) + common k a b c j := by
  cases k <;> fin_cases i <;> fin_cases j <;>
    simp [exponents, monomials, signature, common, Fin.sum_univ_succ] <;> ring

theorem determinant (k : Kind) (a b c : ℤ) :
    (exponents k a b c).det = degree k a b c := by
  cases k <;> simp [exponents, degree, Matrix.det_fin_three] <;> ring

theorem multiplicity (k : Kind) (a b c : ℤ) :
    defect k a b c * degree k a b c * (∏ j, signature k a b c j) =
      (∏ j, weights k a b c j) *
      ((∏ j, signature k a b c j) -
        (signature k a b c 1 * signature k a b c 2 +
         signature k a b c 0 * signature k a b c 2 +
         signature k a b c 0 * signature k a b c 1)) := by
  cases k <;> simp [defect, degree, weights, signature, Fin.sum_univ_succ,
    Fin.prod_univ_succ] <;> ring

theorem group_order (k : Kind) (a b c : ℤ) :
    (monomials k a b c).det * (∏ j, weights k a b c j) =
      degree k a b c * (∏ j, signature k a b c j) := by
  cases k <;> simp [monomials, degree, weights, signature, Matrix.det_fin_three,
    Fin.prod_univ_succ] <;> ring

end CanonicalRoots.Cox
