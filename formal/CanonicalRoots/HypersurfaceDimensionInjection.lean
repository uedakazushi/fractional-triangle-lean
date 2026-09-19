import CanonicalRoots.RootDimension
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- A surjection from a domain hypersurface in three variables to an actual ternary root ring
cannot have a nonzero kernel: that would force a second strict dimension drop. -/
theorem hypersurface_surjection_injective {a : ℕ} (p : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (f : MvPolynomial (Fin 3) ℂ) (hf : f ≠ 0)
    [IsDomain (PresentedRing f)] (φ : PresentedRing f →ₐ[ℂ] RootRing p τ)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  have hdim : ringKrullDim (PresentedRing f) + 1 ≤ (3 : WithBot ℕ∞) := by
    simpa [PresentedRing] using
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf)
  apply (injective_iff_map_eq_zero φ.toRingHom).mpr
  intro x hx
  by_contra hn
  have hlower : (3 : WithBot ℕ∞) ≤ ringKrullDim (PresentedRing f) := by
    have hh := ringKrullDim_succ_le_of_surjective φ.toRingHom hφ
      (mem_nonZeroDivisors_of_ne_zero hn) hx
    rw [canonicalRoot_krullDim p hp ha τ hτ] at hh
    norm_num at hh ⊢
    exact hh
  have hbad := (add_le_add hlower (le_refl (1 : WithBot ℕ∞))).trans hdim
  norm_num at hbad

end CanonicalRoots
