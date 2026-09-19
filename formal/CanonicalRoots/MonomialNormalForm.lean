import CanonicalRoots.DegreeNormalForm

noncomputable section
namespace CanonicalRoots

/-- Integral normal form of a monomial degree, in the original group with torsion. -/
theorem monomialDegree_normal {n : ℕ} (p : Fin n → ℕ) (d : Fin n →₀ ℕ) :
    Finsupp.weight (xDegree p) d = normalDegree p
      (∑ i, (d i / p i : ℕ)) (fun i => (d i % p i : ℕ)) := by
  rw [Finsupp.weight_eq_sum, normalDegree_expression]
  rw [← Nat.cast_sum]
  simp only [natCast_zsmul]
  rw [← Finset.sum_nsmul_assoc]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← degree_relation p i]
  simp only [natCast_zsmul]
  rw [← mul_nsmul, ← add_nsmul]
  congr 1
  exact (Nat.div_add_mod (d i) (p i)).symm

theorem monomialDegree_eq_normal_iff {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (d : Fin n →₀ ℕ) (b : ℤ) (e : Fin n → ℤ)
    (he : ∀ i, 0 ≤ e i ∧ e i < p i) :
    Finsupp.weight (xDegree p) d = normalDegree p b e ↔
      (∑ i, (d i / p i : ℕ) : ℤ) = b ∧ ∀ i, (d i % p i : ℕ) = e i := by
  rw [monomialDegree_normal]
  constructor
  · intro h
    obtain ⟨hb, heq⟩ := degree_normal_unique p hp _ _ _ _
      (fun i => ⟨by positivity, by exact_mod_cast Nat.mod_lt (d i) (hp i)⟩) he h
    exact ⟨hb, fun i => congrFun heq i⟩
  · rintro ⟨hb, heq⟩
    rw [hb, funext heq]

end CanonicalRoots
