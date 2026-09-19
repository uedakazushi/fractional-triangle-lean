import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Push

noncomputable section
namespace CanonicalRoots

/-- An invertible linear coordinate matrix contains a nonzero permutation diagonal. -/
theorem linearEquiv_coordinate_matching {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, e (Pi.single i 1) (σ i) ≠ 0 := by
  classical
  let M := LinearMap.toMatrix' e.toLinearMap
  let N := LinearMap.toMatrix' e.symm.toLinearMap
  have hmul : M * N = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => e.apply_symm_apply x
    rw [he, LinearMap.toMatrix'_id]
  have hdet : M.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hmul
  have hex : ∃ σ : Equiv.Perm (Fin n), ∏ i, M (σ i) i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hdet
    simp only [Matrix.det_apply, hn, smul_zero, Finset.sum_const_zero]
  obtain ⟨σ, hσ⟩ := hex
  refine ⟨σ, fun i hi => hσ ?_⟩
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

end CanonicalRoots
