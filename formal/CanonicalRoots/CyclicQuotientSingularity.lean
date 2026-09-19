import CanonicalRoots.HypersurfaceNonregular

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- The transverse cyclic quotient equation, allowing additional free coordinates. -/
def cyclicQuotientEquation {n : ℕ} (i j k : Fin n) (s : ℕ) : MvPolynomial (Fin n) ℂ :=
  X i * X j - X k ^ s

theorem cyclicQuotientEquation_noConstantOrLinear {n : ℕ} (i j k : Fin n) (s : ℕ)
    (hs : 2 ≤ s) : HasNoConstantOrLinear (cyclicQuotientEquation i j k s) := by
  apply (noConstantOrLinear_iff_mem_square _).mpr
  have hx (t : Fin n) : (X t : MvPolynomial (Fin n) ℂ) ∈ polynomialOriginIdeal n := by
    rw [mem_polynomialOriginIdeal_iff]
    simp
  apply Ideal.sub_mem
  · simpa [pow_two] using Ideal.mul_mem_mul (hx i) (hx j)
  · exact Ideal.pow_le_pow_right hs (Ideal.pow_mem_pow (hx k) s)

theorem cyclicQuotientEquation_ne_zero {n : ℕ} (i j k : Fin n) (s : ℕ)
    (hs : 2 ≤ s) (hik : i ≠ k) (hjk : j ≠ k) : cyclicQuotientEquation i j k s ≠ 0 := by
  intro hz
  have h := congrArg (eval (fun t : Fin n => if t = k then (0 : ℂ) else 1)) hz
  have hs0 : s ≠ 0 := by omega
  simp [cyclicQuotientEquation, hik, hjk, hs0] at h

/-- The localization at the origin of `C[U,V,W,...]/(UV-W^s)` is not regular for `s ≥ 2`.
The connection from a stabilizer invariant ring to this presentation is a separate obligation. -/
theorem cyclicQuotient_origin_not_regular {n : ℕ} (i j k : Fin n) (s : ℕ)
    (hs : 2 ≤ s) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ IsRegularLocalRing (PresentedOriginLocalRing (cyclicQuotientEquation i j k s)
      (cyclicQuotientEquation_noConstantOrLinear i j k s hs).1) :=
  presented_origin_not_regular _ (cyclicQuotientEquation_noConstantOrLinear i j k s hs)
    (cyclicQuotientEquation_ne_zero i j k s hs hik hjk)

theorem RootHypersurfacePresentation.origin_not_regular {n : ℕ} {p : Fin n → ℕ}
    {τ : DegreeGroup p} (H : RootHypersurfacePresentation p τ) :
    ¬ IsRegularLocalRing (PresentedOriginLocalRing H.polynomial H.no_constant_or_linear.1) :=
  presented_origin_not_regular H.polynomial H.no_constant_or_linear H.polynomial_ne_zero

end CanonicalRoots
