import CanonicalRoots.PowerSeriesDiagonalFixed
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
namespace CanonicalRoots

variable {σ G : Type*} (w : G → σ → ℂ)
local instance : DecidableEq σ := Classical.decEq _

def DiagonalInvariantExponent (d : σ →₀ ℕ) : Prop :=
  ∀ g : G, d.prod (fun i k => w g i ^ k) = 1

/-- An invariant exponent that cannot split into two nonzero invariant exponents. -/
def DiagonalIndecomposableExponent (d : σ →₀ ℕ) : Prop :=
  d ≠ 0 ∧ DiagonalInvariantExponent w d ∧
    ∀ e f : σ →₀ ℕ, e + f = d → DiagonalInvariantExponent w e → DiagonalInvariantExponent w f →
      e = 0 ∨ f = 0

abbrev powerSeriesDiagonalOriginIdeal := RingHom.ker (powerSeriesDiagonalOrigin w).toRingHom

def diagonalOriginCoefficient (d : σ →₀ ℕ) : powerSeriesDiagonalOriginIdeal w →ₗ[ℂ] ℂ :=
  (MvPowerSeries.coeff d).comp ((powerSeriesDiagonalFixed w).val.toLinearMap.comp
    ((powerSeriesDiagonalOriginIdeal w).subtype.restrictScalars ℂ))

@[simp] theorem diagonalOriginCoefficient_apply (d : σ →₀ ℕ) (f : powerSeriesDiagonalOriginIdeal w) :
    diagonalOriginCoefficient w d f = MvPowerSeries.coeff d f.val.val := rfl

/-- An indecomposable invariant exponent's coefficient vanishes on the square of the augmentation ideal. -/
theorem diagonalOriginCoefficient_mul (d : σ →₀ ℕ) (hd : DiagonalIndecomposableExponent w d)
    (f g : powerSeriesDiagonalOriginIdeal w) : diagonalOriginCoefficient w d (f * g) = 0 := by
  classical
  change MvPowerSeries.coeff d (f.val.val * g.val.val) = 0
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ef hef
  have hef' : ef.1 + ef.2 = d := Finset.mem_antidiagonal.mp hef
  by_cases hf : MvPowerSeries.coeff ef.1 f.val.val = 0
  · simp only [hf, zero_mul]
  by_cases hg : MvPowerSeries.coeff ef.2 g.val.val = 0
  · simp only [hg, mul_zero]
  have hfi : DiagonalInvariantExponent w ef.1 :=
    (mem_powerSeriesDiagonalFixed_iff w f.val.val).mp f.val.property ef.1 hf
  have hgi : DiagonalInvariantExponent w ef.2 :=
    (mem_powerSeriesDiagonalFixed_iff w g.val.val).mp g.val.property ef.2 hg
  rcases hd.2.2 ef.1 ef.2 hef' hfi hgi with he | he
  · have hz : MvPowerSeries.coeff 0 f.val.val = 0 := f.property
    exact (hf (he ▸ hz)).elim
  · have hz : MvPowerSeries.coeff 0 g.val.val = 0 := g.property
    exact (hg (he ▸ hz)).elim

/-- The coefficient functional descends to the actual ideal cotangent module. -/
def diagonalCotangentCoefficient (d : σ →₀ ℕ) (hd : DiagonalIndecomposableExponent w d) :
    (powerSeriesDiagonalOriginIdeal w).Cotangent →ₗ[ℂ] ℂ :=
  Ideal.Cotangent.lift (diagonalOriginCoefficient w d) (diagonalOriginCoefficient_mul w d hd)

def diagonalCotangentMonomial (d : σ →₀ ℕ) (hd : DiagonalIndecomposableExponent w d) :
    (powerSeriesDiagonalOriginIdeal w).Cotangent :=
  (powerSeriesDiagonalOriginIdeal w).toCotangent
    ⟨⟨MvPowerSeries.monomial d 1, monomial_mem_powerSeriesDiagonalFixed w d 1 hd.2.1⟩,
      MvPowerSeries.coeff_monomial_ne (Ne.symm hd.1) 1⟩

@[simp] theorem diagonalCotangentCoefficient_monomial (d e : σ →₀ ℕ)
    (hd : DiagonalIndecomposableExponent w d) (he : DiagonalIndecomposableExponent w e) :
    diagonalCotangentCoefficient w d hd (diagonalCotangentMonomial w e he) =
      if d = e then 1 else 0 := by
  classical
  exact MvPowerSeries.coeff_monomial d e 1

/-- Distinct indecomposable invariant monomials are linearly independent in the actual cotangent space. -/
theorem diagonalCotangentMonomials_linearIndependent {ι : Type*} [Fintype ι]
    (d : ι → σ →₀ ℕ) (hd : ∀ i, DiagonalIndecomposableExponent w (d i)) (hi : Function.Injective d) :
    LinearIndependent ℂ (fun i => diagonalCotangentMonomial w (d i) (hd i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (diagonalCotangentCoefficient w (d i) (hd i)) hc
  simpa only [map_sum, map_smul, map_zero, diagonalCotangentCoefficient_monomial, hi.eq_iff,
    smul_ite, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

end CanonicalRoots
