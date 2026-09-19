import CanonicalRoots.PresentedGradedRename
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Nonsingular integer exponent matrices act surjectively on a complex torus.
This uses the complex exponential and an ordinary matrix inverse, without a
choice of atomic polynomial type. -/
theorem exponent_torus_surjective {n : ℕ} (E : Matrix (Fin n) (Fin n) ℕ)
    (hE : Matrix.det (fun i j : Fin n => (E i j : ℤ)) ≠ 0)
    (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) :
    ∃ s : Fin n → ℂ, (∀ j, s j ≠ 0) ∧ ∀ i, ∏ j, s j ^ E i j = c i := by
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => E i j
  have hA : A.det ≠ 0 := by
    have hcast : A.det =
        ((Matrix.det (fun i j : Fin n => (E i j : ℤ)) : ℤ) : ℂ) := by
      symm
      exact (Int.castRingHom ℂ).map_det _
    rw [hcast]
    exact_mod_cast hE
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)))
      (fun i => Complex.log (c i))
  refine ⟨fun j => Complex.exp (v j), fun _ => Complex.exp_ne_zero _, ?_⟩
  intro i
  calc
    _ = Complex.exp (∑ j, (E i j : ℂ) * v j) := by
      rw [Complex.exp_sum]
      simp only [Complex.exp_nat_mul]
    _ = Complex.exp (Complex.log (c i)) := by
      congr 1
      exact congrFun hv i
    _ = c i := Complex.exp_log (hc i)

def diagonalPolynomialMap {n : ℕ} (s : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (fun i => C (s i) * X i)

theorem diagonalPolynomialMap_monomial {n : ℕ} (s : Fin n → ℂ)
    (d : Fin n →₀ ℕ) (c : ℂ) :
    diagonalPolynomialMap s (monomial d c) =
      monomial d (c * ∏ i, s i ^ d i) := by
  classical
  simp only [diagonalPolynomialMap, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod, map_mul]
  ring

def diagonalPolynomialEquiv {n : ℕ} (s : Fin n → ℂ) (hs : ∀ i, s i ≠ 0) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  AlgEquiv.ofAlgHom (diagonalPolynomialMap s) (diagonalPolynomialMap (fun i => (s i)⁻¹))
    (by
      ext i : 1
      change diagonalPolynomialMap s (diagonalPolynomialMap (fun j => (s j)⁻¹) (X i)) = X i
      simp only [diagonalPolynomialMap, aeval_X, map_mul, aeval_C, algebraMap_eq]
      simp [← mul_assoc, ← map_mul, hs])
    (by
      ext i : 1
      change diagonalPolynomialMap (fun j => (s j)⁻¹) (diagonalPolynomialMap s (X i)) = X i
      simp only [diagonalPolynomialMap, aeval_X, map_mul, aeval_C, algebraMap_eq]
      simp [← mul_assoc, ← map_mul, hs])

theorem diagonalPolynomialMap_homogeneous {n m : ℕ} (s : Fin n → ℂ)
    (w : Fin n → ℕ) {f : MvPolynomial (Fin n) ℂ}
    (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w (diagonalPolynomialMap s f) m := by
  classical
  rw [← support_sum_monomial_coeff f, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [diagonalPolynomialMap_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ (hf (mem_support_iff.mp hd))

/-- Diagonal variable changes induce equivalences of the actual graded quotients. -/
def presentedGradedDiagonal {n : ℕ} (s : Fin n → ℂ) (hs : ∀ i, s i ≠ 0)
    (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ) :
    GradedAlgEquiv (presentedPiece f w) (presentedPiece (diagonalPolynomialMap s f) w) := by
  let e := diagonalPolynomialEquiv s hs
  let q : PresentedRing f ≃ₐ[ℂ] PresentedRing (diagonalPolynomialMap s f) :=
    Ideal.quotientEquivAlg _ _ e (by simp [Ideal.map_span, Set.image_singleton]; rfl)
  refine ⟨q, ?_⟩
  intro m x
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact Submodule.mem_map.mpr ⟨diagonalPolynomialMap s g,
      diagonalPolynomialMap_homogeneous s w hg, rfl⟩
  · rintro ⟨g,hg,he⟩
    refine Submodule.mem_map.mpr ⟨e.symm g,
      diagonalPolynomialMap_homogeneous (fun i => (s i)⁻¹) w hg, ?_⟩
    apply q.injective
    change Ideal.Quotient.mkₐ ℂ _ (e (e.symm g)) = q x
    rw [e.apply_symm_apply]
    exact he

end CanonicalRoots
