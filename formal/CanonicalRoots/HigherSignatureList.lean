import CanonicalRoots.HigherArithmetic
import CanonicalRoots.HigherRealization
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.OfFn

namespace CanonicalRoots

theorem intProduct_ofFn {n : ℕ} (p : Fin n → ℕ) :
    intProduct (List.ofFn p) = ((∏ i, p i : ℕ) : ℤ) := by
  simp [intProduct, List.map_ofFn, List.prod_ofFn, Nat.cast_prod]

theorem productWeights_zero {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0) :
    productWeights p 0 = ∏ i : Fin n, p i.succ := by
  apply Nat.eq_of_mul_eq_mul_right hp
  rw [productWeights_mul, Fin.prod_univ_succ, mul_comm]

theorem productWeights_succ {n : ℕ} (p : Fin (n + 1) → ℕ) (i : Fin n) (hp : 0 < p i.succ) :
    productWeights p i.succ = p 0 * productWeights (fun j : Fin n => p j.succ) i := by
  apply Nat.eq_of_mul_eq_mul_right hp
  rw [productWeights_mul, mul_assoc, productWeights_mul, Fin.prod_univ_succ]

theorem cofactorSum_ofFn {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) :
    cofactorSum (List.ofFn p) = ∑ i, (productWeights p i : ℤ) := by
  induction n with
  | zero => simp [cofactorSum]
  | succ n ih =>
    rw [List.ofFn_succ, cofactorSum, intProduct_ofFn, ih (fun i => p i.succ) (fun i => hp i.succ), Fin.sum_univ_succ,
      productWeights_zero p (hp 0)]
    simp_rw [productWeights_succ p _ (hp _), Nat.cast_mul]
    rw [Finset.mul_sum]

theorem list_ofFn_pairwise_coprime_iff {n : ℕ} (p : Fin n → ℕ) :
    (List.ofFn p).Pairwise Nat.Coprime ↔ Pairwise (fun i j => Nat.Coprime (p i) (p j)) := by
  rw [List.pairwise_ofFn]
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with he | he
    · exact h he
    · exact (h he).symm
  · intro h i j hij
    exact h (ne_of_lt hij)

/-- The arithmetic enumerator's list condition agrees with the independent
finite-coordinate product-defect condition. -/
theorem enumerateHigherCandidates_ofFn_iff {n a : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (ha : 0 < a) :
    List.ofFn p ∈ enumerateHigherCandidates n a ↔
      (∀ i, 2 ≤ p i) ∧ StrictMono p ∧ Pairwise (fun i j => Nat.Coprime (p i) (p j)) ∧
        ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a := by
  rw [enumerateHigherCandidates_iff n a ha]
  simp only [ArithmeticHigher, List.length_ofFn, true_and, List.forall_mem_ofFn_iff,
    list_ofFn_pairwise_coprime_iff, intProduct_ofFn, cofactorSum_ofFn p hp]
  rw [List.pairwise_ofFn]
  rfl

end CanonicalRoots
