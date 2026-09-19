import CanonicalRoots.Target
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- An invertible polynomial in the sense of Definition 1.3 of the manuscript.
The input is an actual polynomial with exactly `n` nonzero monomial terms,
a nonsingular exponent matrix, positive weights, and an isolated critical point.
No atomic normal form or root-ring realization is included in this definition. -/
structure InvertiblePolynomial {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (h : ℕ) where
  exponent : Fin n → (Fin n →₀ ℕ)
  coefficient : Fin n → ℂ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  polynomial_eq : f = ∑ i, monomial (exponent i) (coefficient i)
  determinant_ne_zero : Matrix.det (fun i j : Fin n => (exponent i j : ℤ)) ≠ 0
  weights_pos : ∀ i, 0 < w i
  degree_pos : 0 < h
  homogeneous : IsWeightedHomogeneous w f h
  no_constant_or_linear : HasNoConstantOrLinear f
  isolated : IsolatedAtOrigin f

def InvertiblePolynomial.exponentMatrix {n h : ℕ} {f : MvPolynomial (Fin n) ℂ}
    {w : Fin n → ℕ} (F : InvertiblePolynomial f w h) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => F.exponent i j

/-- A principal presentation has the determinant and primitive-weight normalization
required by equation (1.6). The parameter equation is kept explicit in theorems. -/
def InvertiblePolynomial.IsPrincipal {n h : ℕ} {f : MvPolynomial (Fin n) ℂ}
    {w : Fin n → ℕ} (F : InvertiblePolynomial f w h) : Prop :=
  Finset.univ.gcd w = 1 ∧ |F.exponentMatrix.det| = (h : ℤ)

theorem InvertiblePolynomial.exponent_injective {n h : ℕ} {f : MvPolynomial (Fin n) ℂ}
    {w : Fin n → ℕ} (F : InvertiblePolynomial f w h) : Function.Injective F.exponent := by
  intro i j hij
  by_contra hne
  exact F.determinant_ne_zero (Matrix.det_zero_of_row_eq hne (by
    change (fun k => (F.exponent i k : ℤ)) = (fun k => (F.exponent j k : ℤ))
    rw [hij]))

theorem InvertiblePolynomial.coeff_exponent {n h : ℕ} {f : MvPolynomial (Fin n) ℂ}
    {w : Fin n → ℕ} (F : InvertiblePolynomial f w h) (i : Fin n) :
    f.coeff (F.exponent i) = F.coefficient i := by
  classical
  calc
    _ = (∑ j, monomial (F.exponent j) (F.coefficient j)).coeff (F.exponent i) :=
      congrArg (fun g : MvPolynomial (Fin n) ℂ => g.coeff (F.exponent i)) F.polynomial_eq
    _ = _ := by simp [coeff_sum, coeff_monomial, F.exponent_injective.eq_iff]

theorem InvertiblePolynomial.degree_equations {n h : ℕ} {f : MvPolynomial (Fin n) ℂ}
    {w : Fin n → ℕ} (F : InvertiblePolynomial f w h) (i : Fin n) :
    ∑ j, F.exponentMatrix i j * (w j : ℤ) = (h : ℤ) := by
  have he := F.homogeneous (by rw [F.coeff_exponent]; exact F.coefficient_ne_zero i)
  simp only [Finsupp.weight_eq_sum, smul_eq_mul] at he
  change ∑ j, (F.exponent i j : ℤ) * (w j : ℤ) = (h : ℤ)
  exact_mod_cast he

theorem InvertiblePolynomial.exists_exponent_of_coeff_ne_zero {n h : ℕ}
    {f : MvPolynomial (Fin n) ℂ} {w : Fin n → ℕ} (F : InvertiblePolynomial f w h)
    (d : Fin n →₀ ℕ) (hd : f.coeff d ≠ 0) : ∃ i, F.exponent i = d := by
  classical
  by_contra hn
  push Not at hn
  apply hd
  rw [F.polynomial_eq, coeff_sum]
  exact Finset.sum_eq_zero (fun i _ => by simp [coeff_monomial, hn i])

end CanonicalRoots
