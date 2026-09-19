import CanonicalRoots.RootBox

noncomputable section
namespace CanonicalRoots

/-- Separate each bounded exponent into its quotient and residue modulo p_i. -/
def boxCoordinatesEquiv {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i) (u : ℕ) :
    AmbientBox p u ≃ (Fin n → Fin u) × (∀ i, Fin (p i)) where
  toFun q :=
    (fun i => ⟨(q.1 i : ℕ) / p i.succ, (Nat.div_lt_iff_lt_mul (hp i.succ)).mpr (q.1 i).isLt⟩,
      Fin.cons q.2 (fun i => ⟨(q.1 i : ℕ) % p i.succ, Nat.mod_lt _ (hp i.succ)⟩))
  invFun q :=
    (fun i => ⟨p i.succ * (q.1 i : ℕ) + q.2 i.succ, by
      have hq := (q.1 i).isLt
      have hr := (q.2 i.succ).isLt
      nlinarith⟩, q.2 0)
  left_inv q := by
    apply Prod.ext
    · funext i
      apply Fin.ext
      exact Nat.div_add_mod _ _
    · rfl
  right_inv q := by
    apply Prod.ext
    · funext i
      apply Fin.ext
      change (p i.succ * (q.1 i : ℕ) + (q.2 i.succ : ℕ)) / p i.succ = q.1 i
      rw [Nat.mul_add_div (hp i.succ), Nat.div_eq_of_lt (q.2 i.succ).isLt, add_zero]
    · funext i
      refine Fin.cases rfl (fun j => ?_) i
      apply Fin.ext
      change (p j.succ * (q.1 j : ℕ) + (q.2 j.succ : ℕ)) % p j.succ = q.2 j.succ
      simp [Nat.mod_eq_of_lt (q.2 j.succ).isLt]

/-- The carry is the sum of the quotient coordinates; all residues remain in the actual group. -/
theorem boxDegree_coordinates {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i) (u : ℕ)
    (q : (Fin n → Fin u) × (∀ i, Fin (p i))) :
    boxDegree p u ((boxCoordinatesEquiv p hp u).symm q) =
      normalDegree p (∑ i, (q.1 i : ℤ)) (fun i => (q.2 i : ℤ)) := by
  have hs : (∑ i, (q.1 i : ℤ)) • cDegree p = ∑ i, (q.1 i : ℤ) • cDegree p := by
    rw [← Nat.cast_sum]
    simp only [natCast_zsmul, Finset.sum_nsmul_assoc]
  rw [boxDegree_expression, normalDegree_expression, Fin.sum_univ_succ]
  change (q.2 0 : ℤ) • xDegree p 0 +
    ∑ i, ((p i.succ * (q.1 i : ℕ) + (q.2 i.succ : ℕ) : ℕ) : ℤ) • xDegree p i.succ = _
  simp only [Nat.cast_add, Nat.cast_mul, add_zsmul, mul_smul, smul_comm (p _ : ℤ),
    degree_relation, Finset.sum_add_distrib]
  rw [hs]
  abel

/-- Integer root multiples of a monomial necessarily have nonnegative coefficient. -/
theorem box_integer_root_nonnegative {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (u : ℕ) (q : AmbientBox p u) (m : ℤ) (hm : boxDegree p u q = m • τ) : 0 ≤ m := by
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  have hnonneg := monomialDegree_nonnegative p hpos (boxExponent p u q)
  change 0 ≤ rationalDegree p _ (boxDegree p u q) at hnonneg
  rw [hm, map_zsmul] at hnonneg
  have hμ := root_degree_positive p hp ha τ hτ
  have hmq : (0 : ℚ) ≤ m := by
    change 0 ≤ (m : ℚ) * rationalDegree p _ τ at hnonneg
    nlinarith
  exact_mod_cast hmq

theorem box_mem_root_iff_integer {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (u : ℕ) (q : AmbientBox p u) :
    (∃ m : ℕ, boxDegree p u q = m • τ) ↔ ∃ m : ℤ, boxDegree p u q = m • τ := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    have hnonneg := box_integer_root_nonnegative p hp ha τ hτ u q m hm
    refine ⟨m.toNat, ?_⟩
    change boxDegree p u q = (m.toNat : ℤ) • τ
    rw [Int.toNat_of_nonneg hnonneg]
    exact hm

end CanonicalRoots
