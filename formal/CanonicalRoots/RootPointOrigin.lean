import CanonicalRoots.RootPointLocalMap
import CanonicalRoots.TwoCoordinatePoints

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- The origin of the original root subalgebra, obtained by evaluating all ambient coordinates at zero. -/
def rootOriginPoint {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (τ : DegreeGroup p) :
    RootRing p τ →ₐ[ℂ] ℂ :=
  rootPoint p τ (fermatPoint p (fun _ => 0) (by simp [zero_pow (ne_of_gt (hp _))]))

/-- A nonzero ambient coordinate stays away from the origin after the finite quotient. -/
theorem rootPoint_ne_origin_of_coordinate_ne_zero {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (z : AmbientRing p →ₐ[ℂ] ℂ) (i : Fin (n + 1))
    (hi : z (ambientQuotient p (X i)) ≠ 0) :
    rootPoint p τ z ≠ rootOriginPoint p (fun j => lt_of_lt_of_le (by decide) (hp.1 j)) τ := by
  let u := canonicalRootScale p a
  let N := signatureLcm p
  have hN : N • τ = u • cDegree p := canonicalRoot_nat_denominator p hp ha τ hτ
  let r : RootRing p τ := ⟨ambientQuotient p (X i ^ (u * p i)),
    (le_iSup (fun m : ℕ => ambientPiece p (m • τ)) N)
      (rootCoordinatePower_homogeneous p τ N u hN i)⟩
  intro he
  have hr := DFunLike.congr_fun he r
  change z (ambientQuotient p (X i ^ (u * p i))) =
    fermatPoint p (fun _ => 0) (by
      apply Finset.sum_eq_zero
      intro j _
      exact zero_pow (by have := hp.1 j; omega))
      (ambientQuotient p (X i ^ (u * p i))) at hr
  rw [map_pow, map_pow, map_pow, fermatPoint_X] at hr
  have hexp : u * p i ≠ 0 := Nat.ne_of_gt
    (Nat.mul_pos (canonicalRootScale_pos p hp ha τ hτ) (lt_of_lt_of_le (by decide) (hp.1 i)))
  rw [zero_pow hexp] at hr
  exact (pow_ne_zero _ hi) hr

end CanonicalRoots
