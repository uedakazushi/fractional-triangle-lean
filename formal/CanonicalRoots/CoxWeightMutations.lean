import CanonicalRoots.CoxData
import Mathlib.Tactic

namespace CanonicalRoots.Cox

/-- Numerical mutation II(2,2k+1,gamma)/2 to III(2,k+1,gamma). -/
theorem oneArrow_to_twoCycle (k γ : ℤ) :
    degree .II 2 (2*k+1) γ = 2 * degree .III 2 (k+1) γ ∧
      ∀ i, weights .II 2 (2*k+1) γ i = 2 * weights .III 2 (k+1) γ i := by
  constructor
  · simp only [degree]; ring
  · intro i; fin_cases i <;> simp [weights] <;> ring

/-- Numerical mutation II(alpha,2k,2)/2 to IV(alpha,k,2). -/
theorem oneArrow_to_chain (α k : ℤ) :
    degree .II α (2*k) 2 = 2 * degree .IV α k 2 ∧
      ∀ i, weights .II α (2*k) 2 i = 2 * weights .IV α k 2 i := by
  constructor
  · simp only [degree]; ring
  · intro i; fin_cases i <;> simp [weights] <;> ring

/-- Numerical mutation I(2,2k,gamma)/2 to II(k,2,gamma), swapping the first two weights. -/
theorem fermat_to_oneArrow (k γ : ℤ) :
    degree .I 2 (2*k) γ = 2 * degree .II k 2 γ ∧
      ∀ i, weights .I 2 (2*k) γ (Equiv.swap 0 1 i) = 2 * weights .II k 2 γ i := by
  constructor
  · simp only [degree]; ring
  · intro i; fin_cases i <;> norm_num [weights, Equiv.swap_apply_def] <;> ring

/-- Numerical mutation I(3,3,gamma)/3 to III(2,2,gamma). -/
theorem fermat_to_twoCycle (γ : ℤ) :
    degree .I 3 3 γ = 3 * degree .III 2 2 γ ∧
      ∀ i, weights .I 3 3 γ i = 3 * weights .III 2 2 γ i := by
  constructor
  · simp only [degree]; ring
  · intro i; fin_cases i <;> norm_num [weights] <;> ring

end CanonicalRoots.Cox
