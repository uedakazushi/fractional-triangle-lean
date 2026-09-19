import CanonicalRoots.DegreeNormalForm

noncomputable section
namespace CanonicalRoots

def freeNumerator {n : ℕ} (p : Fin n → ℕ) (N : ℤ) : FreeDegrees n →+ ℤ where
  toFun u := u none * N + ∑ i, u (some i) * (N / (p i : ℤ))
  map_zero' := by simp
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]; ring

@[simp] theorem freeNumerator_c {n : ℕ} (p : Fin n → ℕ) (N : ℤ) :
    freeNumerator p N (Pi.single none 1) = N := by
  simp [freeNumerator]

@[simp] theorem freeNumerator_x {n : ℕ} (p : Fin n → ℕ) (N : ℤ) (i : Fin n) :
    freeNumerator p N (Pi.single (some i) 1) = N / (p i : ℤ) := by
  classical
  simp [freeNumerator, Pi.single_apply, eq_comm]

/-- Integral degree for a common denominator, defined on the original group. -/
def numeratorDegree {n : ℕ} (p : Fin n → ℕ) (N : ℤ) (hN : ∀ i, (p i : ℤ) ∣ N) :
    DegreeGroup p →+ ℤ :=
  QuotientAddGroup.lift (degreeRelations p) (freeNumerator p N) (by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    change freeNumerator p N ((p i : ℤ) • Pi.single (some i) 1 - Pi.single none 1) = 0
    rw [map_sub, map_zsmul, freeNumerator_x, freeNumerator_c]
    change (p i : ℤ) * (N / (p i : ℤ)) - N = 0
    have h := Int.ediv_mul_cancel (hN i)
    nlinarith)

@[simp] theorem numeratorDegree_c {n : ℕ} (p : Fin n → ℕ) (N : ℤ)
    (hN : ∀ i, (p i : ℤ) ∣ N) : numeratorDegree p N hN (cDegree p) = N :=
  freeNumerator_c p N

@[simp] theorem numeratorDegree_x {n : ℕ} (p : Fin n → ℕ) (N : ℤ)
    (hN : ∀ i, (p i : ℤ) ∣ N) (i : Fin n) :
    numeratorDegree p N hN (xDegree p i) = N / (p i : ℤ) := freeNumerator_x p N i

@[simp] theorem numeratorDegree_omega {n : ℕ} (p : Fin n → ℕ) (N : ℤ)
    (hN : ∀ i, (p i : ℤ) ∣ N) :
    numeratorDegree p N hN (omegaDegree p) = N - ∑ i, N / (p i : ℤ) := by
  simp [omegaDegree]

/-- Clearing a common denominator is an equality in L, not just in its rationalization. -/
theorem denominator_omega {n : ℕ} (p : Fin n → ℕ) (N : ℤ)
    (hN : ∀ i, (p i : ℤ) ∣ N) :
    N • omegaDegree p = (N - ∑ i, N / (p i : ℤ)) • cDegree p := by
  have hx : ∀ i, N • xDegree p i = (N / (p i : ℤ)) • cDegree p := by
    intro i
    calc
      N • xDegree p i = (N / (p i : ℤ) * (p i : ℤ)) • xDegree p i := by
        rw [Int.ediv_mul_cancel (hN i)]
      _ = _ := by rw [mul_smul, degree_relation]
  rw [omegaDegree, zsmul_sub, ← Finset.sum_zsmul]
  simp only [hx, Finset.sum_smul, sub_smul]

theorem canonicalRoot_index_dvd {n a : ℕ} (p : Fin n → ℕ) (N : ℤ)
    (hN : ∀ i, (p i : ℤ) ∣ N) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    (a : ℤ) ∣ N - ∑ i, N / (p i : ℤ) := by
  refine ⟨numeratorDegree p N hN τ, ?_⟩
  have h := congrArg (numeratorDegree p N hN) hτ
  change numeratorDegree p N hN (a • τ) = numeratorDegree p N hN (omegaDegree p) at h
  simpa using h.symm

/-- Bezout constructs an actual root whenever the common-denominator index criterion holds. -/
theorem canonicalRoot_of_index {n a : ℕ} (p : Fin n → ℕ) (N : ℤ)
    (hN : ∀ i, (p i : ℤ) ∣ N) (hcop : IsCoprime (a : ℤ) N)
    (hd : (a : ℤ) ∣ N - ∑ i, N / (p i : ℤ)) :
    ∃ τ : DegreeGroup p, IsCanonicalRoot p a τ := by
  obtain ⟨s, t, hst⟩ := hcop
  obtain ⟨k, hk⟩ := hd
  refine ⟨s • omegaDegree p + (t * k) • cDegree p, ?_⟩
  change (a : ℤ) • (s • omegaDegree p + (t * k) • cDegree p) = omegaDegree p
  calc
    _ = (s * (a : ℤ)) • omegaDegree p + t • (((a : ℤ) * k) • cDegree p) := by
      simp only [zsmul_add, smul_smul]
      congr 1 <;> congr 1 <;> ring
    _ = (s * (a : ℤ)) • omegaDegree p + t • (N • omegaDegree p) := by
      rw [← hk, denominator_omega p N hN]
    _ = (s * (a : ℤ) + t * N) • omegaDegree p := by rw [smul_smul, add_zsmul]
    _ = _ := by rw [hst, one_smul]

def signatureLcm {n : ℕ} (p : Fin n → ℕ) : ℕ := Finset.univ.lcm p
def signatureIndex {n : ℕ} (p : Fin n → ℕ) : ℤ :=
  (signatureLcm p : ℤ) - ∑ i, (signatureLcm p : ℤ) / (p i : ℤ)

theorem signature_dvd_lcm {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : p i ∣ signatureLcm p :=
  Finset.dvd_lcm (Finset.mem_univ i)

theorem signature_lcm_pos {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) :
    0 < signatureLcm p := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro i hi
  exact ne_of_gt (hp i)

theorem canonicalRoot_coprime_lcm {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) : Nat.Coprime a (signatureLcm p) := by
  have hprod : IsCoprime (a : ℤ) (∏ i, (p i : ℤ)) :=
    IsCoprime.prod_right (fun i _ => canonicalRoot_coprime p hp τ hτ i)
  have hdiv : signatureLcm p ∣ ∏ i, p i :=
    Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem p hi)
  have hdiv' : (signatureLcm p : ℤ) ∣ ∏ i, (p i : ℤ) := by exact_mod_cast hdiv
  exact (hprod.of_isCoprime_of_dvd_right hdiv').natCoprime

/-- The manuscript's exact existence criterion for roots in the torsion-retaining group. -/
theorem canonicalRoot_exists_iff {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) :
    (∃ τ : DegreeGroup p, IsCanonicalRoot p a τ) ↔
      (a : ℤ) ∣ signatureIndex p ∧ Nat.Coprime a (signatureLcm p) := by
  have hN : ∀ i, (p i : ℤ) ∣ (signatureLcm p : ℤ) := fun i => by
    exact_mod_cast signature_dvd_lcm p i
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨canonicalRoot_index_dvd p _ hN τ hτ, canonicalRoot_coprime_lcm p hp τ hτ⟩
  · rintro ⟨hd, hcop⟩
    exact canonicalRoot_of_index p _ hN hcop.isCoprime hd

/-- The denominator multiple of an actual root, with the quotient computed in integers. -/
theorem canonicalRoot_denominator {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 0 < a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    (signatureLcm p : ℤ) • τ = (signatureIndex p / (a : ℤ)) • cDegree p := by
  have hN : ∀ i, (p i : ℤ) ∣ (signatureLcm p : ℤ) := fun i => by
    exact_mod_cast signature_dvd_lcm p i
  have hd := canonicalRoot_index_dvd p _ hN τ hτ
  have hmul : (a : ℤ) * (signatureIndex p / (a : ℤ)) = signatureIndex p :=
    Int.mul_ediv_cancel' hd
  apply degree_nsmul_injective p hp ha (canonicalRoot_coprime p hp τ hτ)
  change (a : ℤ) • ((signatureLcm p : ℤ) • τ) =
    (a : ℤ) • ((signatureIndex p / (a : ℤ)) • cDegree p)
  calc
    _ = (signatureLcm p : ℤ) • ((a : ℤ) • τ) := smul_comm _ _ _
    _ = (signatureLcm p : ℤ) • omegaDegree p := by rw [show (a : ℤ) • τ = omegaDegree p from hτ]
    _ = signatureIndex p • cDegree p := denominator_omega p _ hN
    _ = _ := by rw [← mul_smul, hmul]

end CanonicalRoots
