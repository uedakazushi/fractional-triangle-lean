import CanonicalRoots.Target
import Mathlib.Algebra.Module.Equiv.Basic

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Degree-m linear maps between shifted rank-one graded polynomial modules.
The source generator has degree s, and the target generator has degree t. -/
def shiftedPolynomialHomPiece {n : ℕ} (w : Fin n → ℕ) (s t m : ℤ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ →ₗ[MvPolynomial (Fin n) ℂ] MvPolynomial (Fin n) ℂ) where
  carrier := {g | ∀ k : ℤ, ∀ v, IsWeightedHomogeneous (fun i => (w i : ℤ)) v (k - s) →
    IsWeightedHomogeneous (fun i => (w i : ℤ)) (g v) (k + m - t)}
  zero_mem' := by
    intro k v hv
    exact isWeightedHomogeneous_zero (R := ℂ) (fun i => (w i : ℤ)) (k + m - t)
  add_mem' := by
    intro f g hf hg k v hv
    exact (hf k v hv).add (hg k v hv)
  smul_mem' := by
    intro c g hg k v hv
    exact (weightedHomogeneousSubmodule ℂ (fun i => (w i : ℤ)) (k + m - t)).smul_mem c (hg k v hv)

theorem mem_shiftedPolynomialHomPiece_iff {n : ℕ} (w : Fin n → ℕ) (s t m : ℤ)
    (g : MvPolynomial (Fin n) ℂ →ₗ[MvPolynomial (Fin n) ℂ] MvPolynomial (Fin n) ℂ) :
    g ∈ shiftedPolynomialHomPiece w s t m ↔
      IsWeightedHomogeneous (fun i => (w i : ℤ)) (g 1) (s + m - t) := by
  constructor
  · intro hg
    exact hg s 1 (by simpa using isWeightedHomogeneous_one (R := ℂ) (fun i => (w i : ℤ)))
  · intro hg k v hv
    have he : g v = v * g 1 := by
      simpa only [smul_eq_mul, mul_one] using g.map_smul v (1 : MvPolynomial (Fin n) ℂ)
    rw [he]
    convert hv.mul hg using 1 <;> ring

theorem shiftedPolynomialHomPiece_map_eval {n : ℕ} (w : Fin n → ℕ) (s t m : ℤ) :
    (shiftedPolynomialHomPiece w s t m).map
      (LinearMap.ringLmapEquivSelf (MvPolynomial (Fin n) ℂ) ℂ (MvPolynomial (Fin n) ℂ)).toLinearMap =
      weightedHomogeneousSubmodule ℂ (fun i => (w i : ℤ)) (s + m - t) := by
  ext v
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (mem_shiftedPolynomialHomPiece_iff w s t m g).mp hg
  · intro hv
    refine ⟨(LinearMap.ringLmapEquivSelf (MvPolynomial (Fin n) ℂ) ℂ
      (MvPolynomial (Fin n) ℂ)).symm v,?_,?_⟩
    · apply (mem_shiftedPolynomialHomPiece_iff w s t m _).mpr
      simpa using hv
    · exact LinearEquiv.apply_symm_apply _ _

theorem integerWeight_eq {n : ℕ} (w : Fin n → ℕ) (d : Fin n →₀ ℕ) :
    Finsupp.weight (fun i => (w i : ℤ)) d = (Finsupp.weight w d : ℤ) := by
  simp [Finsupp.weight_eq_sum, Finsupp.sum, nsmul_eq_mul]

theorem isWeightedHomogeneous_int_iff {n : ℕ} (w : Fin n → ℕ)
    (f : MvPolynomial (Fin n) ℂ) (m : ℕ) :
    IsWeightedHomogeneous (fun i => (w i : ℤ)) f (m : ℤ) ↔ IsWeightedHomogeneous w f m := by
  constructor <;> intro hf d hd
  · have h := hf hd
    rw [integerWeight_eq] at h
    exact_mod_cast h
  · rw [integerWeight_eq]
    exact_mod_cast hf hd

/-- Multiplication by a degree-h equation is a degree-zero differential S(-h) → S. -/
theorem equation_multiplication_degree_zero {n h : ℕ} (w : Fin n → ℕ)
    (f : MvPolynomial (Fin n) ℂ) (hf : IsWeightedHomogeneous w f h) :
    LinearMap.mulLeft (MvPolynomial (Fin n) ℂ) f ∈ shiftedPolynomialHomPiece w h 0 0 := by
  rw [mem_shiftedPolynomialHomPiece_iff]
  simpa using (isWeightedHomogeneous_int_iff w f h).mpr hf

/-- The differential of the dual complex preserves the homogeneous-map degree. -/
theorem dual_equation_differential_preserves {n h : ℕ} (w : Fin n → ℕ)
    (f : MvPolynomial (Fin n) ℂ) (hf : IsWeightedHomogeneous w f h) (t m : ℤ)
    (g : MvPolynomial (Fin n) ℂ →ₗ[MvPolynomial (Fin n) ℂ] MvPolynomial (Fin n) ℂ)
    (hg : g ∈ shiftedPolynomialHomPiece w 0 t m) :
    g.comp (LinearMap.mulLeft (MvPolynomial (Fin n) ℂ) f) ∈ shiftedPolynomialHomPiece w h t m := by
  intro k v hv
  apply hg k
  change IsWeightedHomogeneous (fun i => (w i : ℤ)) (f * v) (k - 0)
  convert ((isWeightedHomogeneous_int_iff w f h).mpr hf).mul hv using 1 <;> ring

end CanonicalRoots
