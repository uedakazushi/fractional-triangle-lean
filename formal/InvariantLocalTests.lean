import CanonicalRoots.InvariantExtension
import CanonicalRoots.RootPointLocalMap

noncomputable section
namespace CanonicalRoots.InvariantLocalTests

/-- No domain, normality, presentation, or invariant-extension assumption is supplied. -/
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    Module.Finite (RootRing p τ) (AmbientRing p) := ambient_finite_over_root p hp ha τ hτ

/-- The local action is a group action on the original localized quotient. -/
example {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (χ : rootPointStabilizer p τ z) (x : AugmentationLocalRing z) :
    pointLocalCharacterAction p τ z χ⁻¹ (pointLocalCharacterAction p τ z χ x) = x := by
  have he := (pointLocalCharacterAction p τ z).map_mul χ⁻¹ χ
  rw [inv_mul_cancel χ, map_one] at he
  exact (DFunLike.congr_fun he x).symm

/-- The localized root inclusion, not just its unlocalized image, is fixed. -/
example {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (χ : rootPointStabilizer p τ z) (r : AugmentationLocalRing (rootPoint p τ z)) :
    pointLocalCharacterAction p τ z χ (rootPointLocalMap p τ z r) = rootPointLocalMap p τ z r :=
  rootPointLocalMap_fixed p τ z χ r

end CanonicalRoots.InvariantLocalTests

#check CanonicalRoots.canonicalRoot_isInvariant
#check CanonicalRoots.ambient_integral_over_root
#check CanonicalRoots.ambient_finite_over_root
#check CanonicalRoots.ambient_primes_over_root_transitive
#check CanonicalRoots.pointLocalCharacterAction
#check CanonicalRoots.rootPointLocalMap_fixed
