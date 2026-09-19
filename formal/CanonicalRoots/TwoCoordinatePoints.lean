import CanonicalRoots.TwoCoordinateStabilizer

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Evaluation at a complex zero of the Fermat polynomial, on the actual quotient. -/
def fermatPoint {n : ℕ} (p : Fin n → ℕ) (v : Fin n → ℂ) (hv : ∑ i, v i ^ p i = 0) :
    AmbientRing p →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (fermatIdeal p) (aeval v) (by
    change Ideal.span {fermat p} ≤ RingHom.ker (aeval v).toRingHom
    rw [Ideal.span_singleton_le_iff_mem]
    change aeval v (fermat p) = 0
    simpa only [fermat, map_sum, map_pow, aeval_X] using hv)

@[simp] theorem fermatPoint_X {n : ℕ} (p : Fin n → ℕ) (v : Fin n → ℂ)
    (hv : ∑ i, v i ^ p i = 0) (i : Fin n) :
    fermatPoint p v hv (ambientQuotient p (X i)) = v i := aeval_X v i

/-- The two-zero-coordinate stratum is nonempty whenever at least two coordinates remain. -/
theorem twoCoordinatePoint_exists {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (hn : 3 ≤ n) (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∃ z : AmbientRing p →ₐ[ℂ] ℂ,
      z (ambientQuotient p (X i)) = 0 ∧ z (ambientQuotient p (X j)) = 0 ∧
      ∀ l, l ≠ i → l ≠ j → z (ambientQuotient p (X l)) ≠ 0 := by
  classical
  have hex : ∃ k : Fin (n + 1), k ∉ ({i, j} : Finset (Fin (n + 1))) := by
    by_contra! he
    have hu : (Finset.univ : Finset (Fin (n + 1))) = {i, j} := by
      ext l
      simp only [Finset.mem_univ, true_iff]
      exact he l
    have hc := congrArg Finset.card hu
    simp [hij] at hc
    omega
  obtain ⟨k, hk⟩ := hex
  have hk' : k ≠ i ∧ k ≠ j := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
  have hki := hk'.1
  have hkj := hk'.2
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (-((n - 2 : ℕ) : ℂ)) (hp k)
  have hy0 : y ≠ 0 := by
    intro he
    rw [he, zero_pow (ne_of_gt (hp k))] at hy
    have hn0 : ((n - 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n - 2 ≠ 0)
    exact hn0 (neg_eq_zero.mp hy.symm)
  let v : Fin (n + 1) → ℂ := fun l => if l = i then 0 else if l = j then 0 else if l = k then y else 1
  have hv : ∑ l, v l ^ p l = 0 := by
    have he (l : Fin (n + 1)) : v l ^ p l = (1 : ℂ) +
        (if l = i then -1 else 0) + (if l = j then -1 else 0) +
        (if l = k then y ^ p k - 1 else 0) := by
      by_cases hli : l = i
      · subst l; simp [v, hij, Ne.symm hki, ne_of_gt (hp i)]
      · by_cases hlj : l = j
        · subst l; simp [v, hli, Ne.symm hkj, ne_of_gt (hp j)]
        · by_cases hlk : l = k
          · subst l; simp [v, hli, hlj]
          · simp [v, hli, hlj, hlk]
    simp_rw [he, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hy]
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  refine ⟨fermatPoint p v hv, ?_, ?_, ?_⟩
  · simp [v]
  · simp [v, Ne.symm hij]
  · intro l hli hlj
    simp only [fermatPoint_X, v, hli, hlj, ↓reduceIte]
    split_ifs <;> simp_all

end CanonicalRoots
