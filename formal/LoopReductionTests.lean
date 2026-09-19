import CanonicalRoots.LoopExponentReduction
import CanonicalRoots.HypersurfaceDimensionInjection

noncomputable section
open CanonicalRoots

example : ArithmeticTernary 7 ⟨.V,2,3,5⟩ := by decide
example (τ : DegreeGroup (candidateSignature ⟨.V,2,3,5⟩))
    (hτ : IsCanonicalRoot (candidateSignature ⟨.V,2,3,5⟩) 7 τ) :
    loopDegreeResidue (by decide : ArithmeticTernary 7 ⟨.V,2,3,5⟩) τ = 0 :=
  loopDegreeResidue_root (by decide) (by decide) τ hτ

-- A residual monomial on the boundary: X^7 Y^4, requiring one Fermat reduction.
example : LoopCongruence 2 3 5 7 4 0 := by norm_num [LoopCongruence]
example : 2 * 3 + 1 ≤ 7 :=
  loop_plane_large (γ := 5) (y := 4) (by decide) (by decide) (by decide)
    (by norm_num [LoopCongruence])
example : LoopCongruence 3 5 2 4 0 7 :=
  loop_congruence_rotate (by norm_num [LoopCongruence] : LoopCongruence 2 3 5 7 4 0)

-- Uniform small-box exclusion, rather than checking a finite list of exponent values.
example {x y z : ℕ} (hx : x < 3) (hy : y < 5) (hz : z < 2)
    (hc : LoopCongruence 2 3 5 x y z) : x = 0 ∧ y = 0 ∧ z = 0 :=
  loop_small_box_zero (by decide) (by decide) (by decide) hx hy hz hc

example {x y z : ℕ} (hc : LoopCongruence 2 3 5 x y z) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨
    (3 ≤ x ∧ 1 ≤ z) ∨ (1 ≤ x ∧ 5 ≤ y) ∨ (1 ≤ y ∧ 2 ≤ z) ∨
    (z = 0 ∧ 7 ≤ x) ∨ (x = 0 ∧ 16 ≤ y) ∨ (y = 0 ∧ 11 ≤ z) :=
  loop_exponent_reduction_cases (by decide) (by decide) (by decide) hc
