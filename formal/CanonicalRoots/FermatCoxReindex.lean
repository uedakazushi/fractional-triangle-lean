import CanonicalRoots.CoxScaledDefect

namespace CanonicalRoots.Cox

theorem fermat_weight_degree (k : Fin 3 → ℤ) (i : Fin 3) :
    k i * weights .I (k 0) (k 1) (k 2) i = degree .I (k 0) (k 1) (k 2) := by
  fin_cases i <;> simp [weights, degree] <;> ring

theorem fermat_degree_reindex (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) :
    degree .I (k (σ 0)) (k (σ 1)) (k (σ 2)) = degree .I (k 0) (k 1) (k 2) := by
  simpa only [degree, Fin.prod_univ_three] using Equiv.prod_comp σ k

theorem fermat_weights_reindex (k : Fin 3 → ℤ) (hk : ∀ i, k i ≠ 0)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    weights .I (k (σ 0)) (k (σ 1)) (k (σ 2)) i = weights .I (k 0) (k 1) (k 2) (σ i) := by
  apply mul_left_cancel₀ (hk (σ i))
  calc
    k (σ i) * weights .I (k (σ 0)) (k (σ 1)) (k (σ 2)) i =
      degree .I (k (σ 0)) (k (σ 1)) (k (σ 2)) := fermat_weight_degree (k ∘ σ) i
    _ = degree .I (k 0) (k 1) (k 2) := fermat_degree_reindex k σ
    _ = k (σ i) * weights .I (k 0) (k 1) (k 2) (σ i) := (fermat_weight_degree k (σ i)).symm

end CanonicalRoots.Cox
