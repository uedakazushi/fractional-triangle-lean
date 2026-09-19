import CanonicalRoots.PowerBoxBasis

noncomputable section
namespace CanonicalRoots

theorem monomialDegree_nonnegative {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (d : Fin n →₀ ℕ) :
    0 ≤ rationalDegree p (fun i => ne_of_gt (hp i)) (Finsupp.weight (xDegree p) d) := by
  simp only [Finsupp.weight_eq_sum, map_sum, map_nsmul, rationalDegree_x, nsmul_eq_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg zero_le_one (Nat.cast_nonneg _)))

/-- A finite box monomial belongs to the root lattice in a nonnegative root degree. -/
def RootBox {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :=
  {q : AmbientBox p u // ∃ m : ℕ, boxDegree p u q = m • τ}

instance {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    Finite (RootBox p τ u) := inferInstanceAs (Finite {_q : AmbientBox p u // _})

def rootBoxDegree {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ)
    (q : RootBox p τ u) : ℕ := q.property.choose

theorem rootBoxDegree_spec {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ)
    (q : RootBox p τ u) : boxDegree p u q.val = rootBoxDegree p τ u q • τ := q.property.choose_spec

/-- The top degree bound and complement identity use positivity of the actual root. -/
theorem rootBox_complement_degree {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u m : ℕ) (hN : N • τ = u • cDegree p) (q : AmbientBox p u)
    (hq : boxDegree p u q = m • τ) :
    m ≤ a + n * N ∧ boxDegree p u (boxComplement p u q) = (a + n * N - m) • τ := by
  have hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  have hsum : m • τ + boxDegree p u (boxComplement p u q) = (a + n * N) • τ := by
    rw [← hq, boxDegree_complement, add_nsmul, hτ]
    congr 1
    calc
      (n * u) • cDegree p = n • (u • cDegree p) := by rw [← mul_nsmul, Nat.mul_comm]
      _ = n • (N • τ) := by rw [hN]
      _ = (n * N) • τ := by rw [← mul_nsmul, Nat.mul_comm]
  have hm : m ≤ a + n * N := by
    have hd := congrArg (rationalDegree p (fun i => ne_of_gt (hpos i))) hsum
    simp only [map_add, map_nsmul, nsmul_eq_mul] at hd
    have hnonneg := monomialDegree_nonnegative p hpos (boxExponent p u (boxComplement p u q))
    change 0 ≤ rationalDegree p _ (boxDegree p u (boxComplement p u q)) at hnonneg
    have hτpos := root_degree_positive p hp ha τ hτ
    have hreal : (m : ℚ) ≤ (a + n * N : ℕ) := by nlinarith
    exact_mod_cast hreal
  refine ⟨hm, ?_⟩
  apply add_left_cancel (a := m • τ)
  rw [← add_nsmul, Nat.add_sub_of_le hm]
  exact hsum

/-- Restricting exponent complementation to the root box is a genuine involution. -/
def rootBoxComplement {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hN : N • τ = u • cDegree p) : RootBox p τ u ≃ RootBox p τ u where
  toFun q := ⟨boxComplement p u q.val, ⟨a + n * N - rootBoxDegree p τ u q,
    (rootBox_complement_degree p hp ha τ hτ N u _ hN q.val (rootBoxDegree_spec p τ u q)).2⟩⟩
  invFun q := ⟨boxComplement p u q.val, ⟨a + n * N - rootBoxDegree p τ u q,
    (rootBox_complement_degree p hp ha τ hτ N u _ hN q.val (rootBoxDegree_spec p τ u q)).2⟩⟩
  left_inv q := by apply Subtype.ext; exact (boxComplement p u).left_inv q.val
  right_inv q := by apply Subtype.ext; exact (boxComplement p u).right_inv q.val

theorem rootBoxDegree_complement {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (q : RootBox p τ u) :
    rootBoxDegree p τ u (rootBoxComplement p hp ha τ hτ N u hN q) =
      a + n * N - rootBoxDegree p τ u q := by
  apply root_multiples_injective p hp ha τ hτ
  change rootBoxDegree p τ u (rootBoxComplement p hp ha τ hτ N u hN q) • τ = _
  rw [← rootBoxDegree_spec]
  exact (rootBox_complement_degree p hp ha τ hτ N u _ hN q.val (rootBoxDegree_spec p τ u q)).2

end CanonicalRoots
