import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Basic.Complex.Basic

noncomputable section
namespace CanonicalRoots

variable {σ G : Type*} (w : G → σ → ℂ)

/-- The actual subalgebra of power series fixed by a family of diagonal substitutions. -/
def powerSeriesDiagonalFixed : Subalgebra ℂ (MvPowerSeries σ ℂ) where
  carrier := {f | ∀ g : G, MvPowerSeries.rescaleAlgHom (w g) f = f}
  algebraMap_mem' c g := (MvPowerSeries.rescaleAlgHom (w g)).commutes c
  zero_mem' g := map_zero _
  one_mem' g := map_one _
  add_mem' hf hh g := by rw [map_add, hf g, hh g]
  mul_mem' hf hh g := by rw [map_mul, hf g, hh g]

/-- Fixedness is the exact coefficient-support condition for the actual diagonal substitutions. -/
theorem mem_powerSeriesDiagonalFixed_iff (f : MvPowerSeries σ ℂ) :
    f ∈ powerSeriesDiagonalFixed w ↔
      ∀ d : σ →₀ ℕ, MvPowerSeries.coeff d f ≠ 0 → ∀ g : G,
        d.prod (fun i k => w g i ^ k) = 1 := by
  constructor
  · intro hf d hd g
    have h := congrArg (MvPowerSeries.coeff d) (hf g)
    rw [MvPowerSeries.rescaleAlgHom_apply, MvPowerSeries.coeff_rescale] at h
    exact mul_right_cancel₀ hd (h.trans (one_mul _).symm)
  · intro hf g
    apply MvPowerSeries.ext
    intro d
    rw [MvPowerSeries.rescaleAlgHom_apply, MvPowerSeries.coeff_rescale]
    by_cases hd : MvPowerSeries.coeff d f = 0
    · rw [hd, mul_zero]
    · rw [hf d hd g, one_mul]

/-- Every invariant monomial is an element of the full fixed power-series ring. -/
theorem monomial_mem_powerSeriesDiagonalFixed (d : σ →₀ ℕ) (c : ℂ)
    (hd : ∀ g : G, d.prod (fun i k => w g i ^ k) = 1) :
    MvPowerSeries.monomial d c ∈ powerSeriesDiagonalFixed w := by
  classical
  apply (mem_powerSeriesDiagonalFixed_iff w _).mpr
  intro e he g
  have hed : e = d := by
    by_contra hne
    exact he (MvPowerSeries.coeff_monomial_ne hne c)
  subst e
  exact hd g

/-- The augmentation is the actual constant coefficient on the fixed subalgebra. -/
def powerSeriesDiagonalOrigin : powerSeriesDiagonalFixed w →ₐ[ℂ] ℂ where
  toRingHom := MvPowerSeries.constantCoeff.comp (powerSeriesDiagonalFixed w).val.toRingHom
  commutes' c := by simp [MvPowerSeries.algebraMap_apply]

@[simp] theorem powerSeriesDiagonalOrigin_apply (f : powerSeriesDiagonalFixed w) :
    powerSeriesDiagonalOrigin w f = MvPowerSeries.coeff 0 f.val := rfl

end CanonicalRoots
