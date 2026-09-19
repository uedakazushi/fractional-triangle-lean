import CanonicalRoots.RootPresentationOrigin
import CanonicalRoots.RootHilbert
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i) (τ : DegreeGroup p)

/-- Degree zero in the actual root ring consists exactly of its complex constants. -/
theorem rootPiece_zero_eq_scalar (z : RootRing p τ) (hz : z ∈ rootPiece p τ 0) :
    z = algebraMap ℂ (RootRing p τ) (rootOriginPoint p hp τ z) := by
  have h1 : (1 : RootRing p τ) ∈ rootPiece p τ 0 := by
    change (1 : AmbientRing p) ∈ ambientPiece p (0 • τ)
    simp only [zero_smul]
    exact Submodule.mem_map.mpr ⟨1, MvPolynomial.isWeightedHomogeneous_one ℂ (xDegree p),
      (ambientQuotient p).map_one⟩
  have hn : (1 : RootRing p τ) ≠ 0 := by
    intro he
    have hh := congrArg (rootOriginPoint p hp τ) he
    exact one_ne_zero (by simpa only [map_one, map_zero] using hh)
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one (rootPiece_zero_finrank p hp τ) h1 hn
  rw [hs] at hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  have hc' : algebraMap ℂ (RootRing p τ) c = z := by
    simpa only [Algebra.smul_def, mul_one] using hc
  rw [← hc']
  simp

variable {a : ℕ} (hpA : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

include hpA ha hτ in
/-- The intrinsic degree-zero projection is evaluation at the original root origin. -/
theorem rootGradedProjection_zero [GradedAlgebra (rootPiece p τ)] (z : RootRing p τ) :
    GradedAlgebra.proj (rootPiece p τ) 0 z =
      algebraMap ℂ (RootRing p τ) (rootOriginPoint p hp τ z) := by
  refine DirectSum.Decomposition.inductionOn (rootPiece p τ) ?_ ?_ ?_ z
  · simp only [map_zero]
  · intro m w
    by_cases hm : m = 0
    · subst m
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ w.property]
      exact rootPiece_zero_eq_scalar p hp τ w w.property
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne _ w.property hm]
      have he := rootOriginPoint_eq_zero_of_positive_piece p τ hpA ha hτ m (by omega) w w.property
      rw [he, map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]

end CanonicalRoots
