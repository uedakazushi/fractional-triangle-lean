import CanonicalRoots.CoprimeRootScale
import CanonicalRoots.RootPointLocalMap

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n a : ℕ} (p : Fin n → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
  (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))

/-- The pure power of exponent `u` as an element of the original root subalgebra. -/
def coprimeRootPurePower (i : Fin n) : RootRing p τ :=
  ⟨ambientQuotient p (X i ^ canonicalRootScale p a), by
    obtain ⟨m, hm⟩ := (pure_power_root_degree_iff p hp ha τ hτ hcop i
      (canonicalRootScale p a)).mpr (dvd_refl _)
    apply le_iSup (fun m : ℕ => ambientPiece p (m • τ)) m
    apply Submodule.mem_map.mpr
    refine ⟨X i ^ canonicalRootScale p a, ?_, rfl⟩
    have he := (isWeightedHomogeneous_X ℂ (xDegree p) i).pow (canonicalRootScale p a)
    rwa [hm] at he⟩

@[simp] theorem coprimeRootPurePower_val (i : Fin n) :
    (coprimeRootPurePower p hp ha τ hτ hcop i : AmbientRing p) =
      ambientQuotient p (X i ^ canonicalRootScale p a) := rfl

@[simp] theorem coprimeRootPurePower_point (z : AmbientRing p →ₐ[ℂ] ℂ) (i : Fin n) :
    rootPoint p τ z (coprimeRootPurePower p hp ha τ hτ hcop i) =
      z (ambientQuotient p (X i)) ^ canonicalRootScale p a := by
  change z (ambientQuotient p (X i ^ canonicalRootScale p a)) = _
  rw [map_pow, map_pow]

end CanonicalRoots
