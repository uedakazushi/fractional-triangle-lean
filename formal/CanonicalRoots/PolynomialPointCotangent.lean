import CanonicalRoots.PolynomialPointCompletion
import CanonicalRoots.HypersurfaceNonregular

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (v : Fin n → ℂ)

/-- Translation identifies the actual cotangent space at any polynomial point. -/
def polynomialPointCotangentEquiv :
    (RingHom.ker (polynomialPoint v).toRingHom).Cotangent ≃ₗ[ℂ] (Fin n → ℂ) := by
  let e := quotientCotangentEquiv (RingHom.ker (polynomialPoint v).toRingHom)
    (polynomialPointTranslation v).toAlgHom (polynomialPointTranslation v).surjective
    (by
      intro x hx
      have he : x = 0 := (polynomialPointTranslation v).injective
        (hx.trans (map_zero _).symm)
      rw [he]
      exact Ideal.zero_mem _)
  exact e.trans (((Ideal.Cotangent.equivOfEq _ _
    (polynomialPointTranslation_map_pointIdeal v)).restrictScalars ℂ).trans
    (polynomialOriginCotangentEquiv n))

theorem polynomialPointCotangent_finrank :
    Module.finrank ℂ (RingHom.ker (polynomialPoint v).toRingHom).Cotangent = n := by
  rw [(polynomialPointCotangentEquiv v).finrank_eq]
  simp

def pointDerivative (i : Fin n) :
    RingHom.ker (polynomialPoint v).toRingHom →ₗ[ℂ] ℂ :=
  (polynomialPoint v).toLinearMap.comp ((pderiv i).toLinearMap.comp
    ((RingHom.ker (polynomialPoint v).toRingHom).subtype.restrictScalars ℂ))

theorem pointDerivative_mul (i : Fin n)
    (f g : RingHom.ker (polynomialPoint v).toRingHom) :
    pointDerivative v i (f * g) = 0 := by
  change polynomialPoint v (pderiv i ((f : MvPolynomial (Fin n) ℂ) * g)) = 0
  rw [pderiv_mul, map_add, map_mul, map_mul]
  have hf : polynomialPoint v f = 0 := f.property
  have hg : polynomialPoint v g = 0 := g.property
  rw [hf, hg, mul_zero, zero_mul, add_zero]

def pointCotangentDerivative (i : Fin n) :
    (RingHom.ker (polynomialPoint v).toRingHom).Cotangent →ₗ[ℂ] ℂ :=
  Ideal.Cotangent.lift (pointDerivative v i) (pointDerivative_mul v i)

/-- A nonzero evaluated partial derivative detects a nonzero actual cotangent class. -/
theorem pointCotangent_ne_zero_of_derivative (f : MvPolynomial (Fin n) ℂ)
    (hf : polynomialPoint v f = 0) (i : Fin n)
    (hi : polynomialPoint v (pderiv i f) ≠ 0) :
    (RingHom.ker (polynomialPoint v).toRingHom).toCotangent ⟨f, hf⟩ ≠ 0 := by
  intro h
  apply hi
  have he := congrArg (pointCotangentDerivative v i) h
  exact he.trans (map_zero _)

end CanonicalRoots
