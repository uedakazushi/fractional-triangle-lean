import CanonicalRoots.RootMonomialBasis
import CanonicalRoots.RootPointOrigin
import CanonicalRoots.AugmentationCotangentSpan

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i) (τ : DegreeGroup p)

def rootMonomialExponent (q : RootMonomialIndex p τ) : Fin (n + 1) →₀ ℕ :=
  q.val.1.cons (q.val.2 : ℕ)

theorem rootMonomialBasis_eq_one_of_exponent_zero (q : RootMonomialIndex p τ)
    (hq : rootMonomialExponent p τ q = 0) : rootMonomialBasis p (hp 0) τ q = 1 := by
  apply Subtype.ext
  rw [rootMonomialBasis_apply, ambientMonomialBasis_apply]
  change ambientQuotient p (monomial (rootMonomialExponent p τ q) 1) = 1
  rw [hq, monomial_zero', C_1, map_one]

theorem rootMonomialBasis_origin_of_exponent_ne_zero (q : RootMonomialIndex p τ)
    (hq : rootMonomialExponent p τ q ≠ 0) :
    rootOriginPoint p hp τ (rootMonomialBasis p (hp 0) τ q) = 0 := by
  change fermatPoint p (fun _ => 0) (by simp [zero_pow (ne_of_gt (hp _))])
    (rootMonomialBasis p (hp 0) τ q : AmbientRing p) = 0
  rw [rootMonomialBasis_apply, ambientMonomialBasis_apply]
  change aeval (fun _ : Fin (n + 1) => (0 : ℂ)) (monomial (rootMonomialExponent p τ q) 1) = 0
  simp only [show (fun _ : Fin (n + 1) => (0 : ℂ)) = 0 from rfl, aeval_zero,
    Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_eq, coeff_monomial, hq, ite_false]

theorem rootMonomial_nonzero_cotangent_exponent (q : RootMonomialIndex p τ)
    (hq : augmentationCotangentProjection (rootOriginPoint p hp τ)
      (rootMonomialBasis p (hp 0) τ q) ≠ 0) : rootMonomialExponent p τ q ≠ 0 := by
  intro hz
  apply hq
  rw [rootMonomialBasis_eq_one_of_exponent_zero p hp τ q hz]
  change (RingHom.ker (rootOriginPoint p hp τ).toRingHom).toCotangent
    (augmentationProjection (rootOriginPoint p hp τ) 1) = 0
  have h : augmentationProjection (rootOriginPoint p hp τ) 1 = 0 := by
    apply Subtype.ext
    simp only [augmentationProjection_apply, map_one, sub_self, ZeroMemClass.coe_zero]
  rw [h, map_zero]

end CanonicalRoots
