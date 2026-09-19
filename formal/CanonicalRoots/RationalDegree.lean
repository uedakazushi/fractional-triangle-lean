import CanonicalRoots.CoxDegrees

noncomputable section
namespace CanonicalRoots

/-- A degree map used as an invariant, never as a replacement for the quotient group. -/
def freeRationalDegree {n : ℕ} (p : Fin n → ℕ) : FreeDegrees n →+ ℚ where
  toFun u := (u none : ℚ) + ∑ i, (u (some i) : ℚ)/(p i : ℚ)
  map_zero' := by simp
  map_add' u v := by simp [add_div, Finset.sum_add_distrib]; ring

@[simp] theorem freeRationalDegree_c {n : ℕ} (p : Fin n → ℕ) :
    freeRationalDegree p (Pi.single none 1) = 1 := by
  simp [freeRationalDegree, Pi.single_apply]

@[simp] theorem freeRationalDegree_x {n : ℕ} (p : Fin n → ℕ) (i : Fin n) :
    freeRationalDegree p (Pi.single (some i) 1) = 1/(p i : ℚ) := by
  classical
  simp [freeRationalDegree, Pi.single_apply, ite_div, eq_comm]

def rationalDegree {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 0) : DegreeGroup p →+ ℚ :=
  QuotientAddGroup.lift (degreeRelations p) (freeRationalDegree p) (by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i,rfl⟩
    change freeRationalDegree p ((p i : ℤ) • Pi.single (some i) 1 - Pi.single none 1) = 0
    rw [map_sub, map_zsmul, freeRationalDegree_x, freeRationalDegree_c]
    have hi : (p i : ℚ) ≠ 0 := by exact_mod_cast hp i
    simp [zsmul_eq_mul, hi])

@[simp] theorem rationalDegree_c {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 0) :
    rationalDegree p hp (cDegree p) = 1 := freeRationalDegree_c p

@[simp] theorem rationalDegree_x {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 0) (i : Fin n) :
    rationalDegree p hp (xDegree p i) = 1/(p i : ℚ) := freeRationalDegree_x p i

@[simp] theorem rationalDegree_omega {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 0) :
    rationalDegree p hp (omegaDegree p) = 1 - ∑ i, (1 : ℚ)/p i := by
  simp [omegaDegree]

theorem root_degree_positive {n a : ℕ} (p : Fin n → ℕ) (hp : AdmissibleSignature p)
    (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    0 < rationalDegree p (fun i => by have := hp.1 i; omega) τ := by
  let hnonzero : ∀ i, p i ≠ 0 := fun i => by have := hp.1 i; omega
  have h := congrArg (rationalDegree p hnonzero) hτ
  change rationalDegree p hnonzero (a • τ) = rationalDegree p hnonzero (omegaDegree p) at h
  rw [map_nsmul, rationalDegree_omega, nsmul_eq_mul] at h
  have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hsum := hp.2
  change 0 < rationalDegree p hnonzero τ
  nlinarith

/-- Distinct natural root degrees stay distinct in L; torsion in L is still retained. -/
theorem root_multiples_injective {n a : ℕ} (p : Fin n → ℕ) (hp : AdmissibleSignature p)
    (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    Function.Injective (fun m : ℕ => m • τ) := by
  intro m k hmk
  let hnonzero : ∀ i, p i ≠ 0 := fun i => by have := hp.1 i; omega
  have h := congrArg (rationalDegree p hnonzero) hmk
  simp only [map_nsmul, nsmul_eq_mul] at h
  have hpos := root_degree_positive p hp ha τ hτ
  have heq : (m : ℚ) = k := mul_right_cancel₀ (ne_of_gt hpos) h
  exact_mod_cast heq

end CanonicalRoots
