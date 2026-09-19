import CanonicalRoots.RootHilbertSeries
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section
namespace CanonicalRoots

local instance rootBoxPolynomialFintype {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    Fintype (RootBox p τ u) := Fintype.ofFinite _

/-- The numerator of the actual root Hilbert series, as a finite polynomial. -/
def rootBoxPolynomial {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    Polynomial ℚ := ∑ q : RootBox p τ u, Polynomial.X ^ rootBoxDegree p τ u q

theorem rootBoxPolynomial_coe {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    (rootBoxPolynomial p τ u : PowerSeries ℚ) = rootBoxNumerator p τ u := by
  change Polynomial.coeToPowerSeries.ringHom (rootBoxPolynomial p τ u) = _
  simp [rootBoxPolynomial, rootBoxNumerator, map_sum]

section Root
variable {n a : ℕ} (p : Fin (n + 1) → ℕ)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p) (hNpos : 0 < N)

include hp ha hτ hu hN hNpos in
theorem rootBoxPolynomial_coeff_zero : (rootBoxPolynomial p τ u).coeff 0 = 1 := by
  have he := congrArg PowerSeries.constantCoeff
    (rootHilbertSeries_mul_denominator p hp ha τ hτ N u hu hN hNpos)
  rw [← rootBoxPolynomial_coe] at he
  simpa [rootHilbertSeries, ne_of_gt hNpos,
    rootPiece_zero_finrank p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ] using he.symm

include hp ha hτ hN in
theorem rootBoxPolynomial_coeff_top_eq_coeff_zero :
    (rootBoxPolynomial p τ u).coeff (a + n * N) = (rootBoxPolynomial p τ u).coeff 0 := by
  classical
  unfold rootBoxPolynomial
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  calc
    _ = ∑ q : RootBox p τ u,
        (Polynomial.X ^ rootBoxDegree p τ u (rootBoxComplement p hp ha τ hτ N u hN q) :
          Polynomial ℚ).coeff (a + n * N) :=
      ((rootBoxComplement p hp ha τ hτ N u hN).sum_comp
        (fun q => (Polynomial.X ^ rootBoxDegree p τ u q : Polynomial ℚ).coeff (a + n * N))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      have hb := (rootBox_complement_degree p hp ha τ hτ N u _ hN q.val
        (rootBoxDegree_spec p τ u q)).1
      rw [rootBoxDegree_complement p hp ha τ hτ N u hN]
      simp only [Polynomial.coeff_X_pow]
      by_cases hd : rootBoxDegree p τ u q = 0
      · simp [hd]
      · have hh : a + n * N ≠ a + n * N - rootBoxDegree p τ u q := by omega
        simp [hh, Ne.symm hd]

include hp ha hτ hu hN hNpos in
theorem rootBoxPolynomial_ne_zero : rootBoxPolynomial p τ u ≠ 0 := by
  intro he
  have hc := rootBoxPolynomial_coeff_zero p hp ha τ hτ N u hu hN hNpos
  rw [he, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

include hp ha hτ hu hN hNpos in
/-- Complementation and the actual degree-zero dimension determine the exact top degree. -/
theorem rootBoxPolynomial_natDegree : (rootBoxPolynomial p τ u).natDegree = a + n * N := by
  classical
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold rootBoxPolynomial
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q _
    rw [Polynomial.natDegree_X_pow]
    exact (rootBox_complement_degree p hp ha τ hτ N u _ hN q.val
      (rootBoxDegree_spec p τ u q)).1
  · rw [rootBoxPolynomial_coeff_top_eq_coeff_zero p hp ha τ hτ N u hN,
      rootBoxPolynomial_coeff_zero p hp ha τ hτ N u hu hN hNpos]
    exact one_ne_zero

end Root
end CanonicalRoots
