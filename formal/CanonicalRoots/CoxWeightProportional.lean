import CanonicalRoots.CoxIdentities
import CanonicalRoots.NumericAxisWeights
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

namespace CanonicalRoots.Cox

theorem degree_pos (kind : Kind) (α β γ : ℤ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ) :
    0 < degree kind α β γ := by
  have hα0 : 0 < α := by omega
  have hβ0 : 0 < β := by omega
  have hγ0 : 0 < γ := by omega
  have hab : 0 < α * β - 1 := by nlinarith [mul_nonneg (by omega : 0 ≤ α - 2) (by omega : 0 ≤ β - 2)]
  cases kind <;> simp only [degree] <;> positivity

theorem weights_pos (kind : Kind) (α β γ : ℤ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (i : Fin 3) : 0 < weights kind α β γ i := by
  have hα0 : 0 < α := by omega
  have hβ0 : 0 < β := by omega
  have hγ0 : 0 < γ := by omega
  have hα1 : 0 < α - 1 := by omega
  have hβ1 : 0 < β - 1 := by omega
  have hγ1 : 0 < γ - 1 := by omega
  have hab : 0 < α * β - 1 := by nlinarith [mul_nonneg (by omega : 0 ≤ α - 2) (by omega : 0 ≤ β - 2)]
  cases kind <;> fin_cases i <;> simp [weights] <;> first | positivity | linarith

/-- Matrix injectivity reuses the verified Cox homogeneous vector and determinant. -/
theorem weight_proportional (kind : Kind) (α β γ h : ℤ) (w : Fin 3 → ℤ)
    (hdeg : degree kind α β γ ≠ 0)
    (hh : ∀ i, ∑ j, exponents kind α β γ i j * w j = h) :
    ∀ i, degree kind α β γ * w i = h * weights kind α β γ i := by
  have heq : degree kind α β γ • w = h • weights kind α β γ := by
    apply Matrix.mulVec_injective_of_det_ne_zero (M := exponents kind α β γ)
      (by rw [determinant]; exact hdeg)
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hh, homogeneous]
    ring
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun heq i

end CanonicalRoots.Cox

namespace CanonicalRoots

def axisKind (tag : Fin 5) : Cox.Kind := ![Cox.Kind.I, .II, .III, .IV, .V] tag

theorem axisKind_homogeneous (tag : Fin 5) (k w : Fin 3 → ℕ) (h : ℕ)
    (hh : ∀ i, axisWeight w i (threeAxisPattern ⟨tag.val, by omega⟩ i) (k i) = h) :
    ∀ i, ∑ j, Cox.exponents (axisKind tag) (k 0) (k 1) (k 2) i j * (w j : ℤ) = h := by
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  fin_cases tag <;> intro i <;> fin_cases i <;>
    simp [axisWeight, threeAxisPattern, axisKind, Cox.exponents, Fin.sum_univ_three] at h0 h1 h2 ⊢ <;>
    norm_cast <;> omega

end CanonicalRoots
