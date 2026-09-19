import CanonicalRoots.BoxCoordinates

noncomputable section
namespace CanonicalRoots

def rootResidueVector {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (σ : Fin n → ℤ) (m : ℕ) : ∀ i, Fin (p i) := fun i =>
  ⟨(rootResidue p σ m i).toNat, by
    have h := rootResidue_bounded p hp σ m i
    omega⟩

@[simp] theorem rootResidueVector_cast {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (σ : Fin n → ℤ) (m : ℕ) (i : Fin n) :
    ((rootResidueVector p hp σ m i : ℕ) : ℤ) = rootResidue p σ m i :=
  Int.toNat_of_nonneg (rootResidue_bounded p hp σ m i).1

/-- The period reduction records both the bounded residues and the exact change of carry. -/
theorem rootCarry_residue_mod {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℤ) (σ : Fin n → ℤ) (N m : ℕ) (u : ℤ)
    (hN : N • normalDegree p b σ = u • cDegree p) :
    rootCarry p b σ m = rootCarry p b σ (m % N) + (m / N : ℕ) * u ∧
      rootResidue p σ m = rootResidue p σ (m % N) := by
  apply degree_normal_unique p hp _ _ _ _ (rootResidue_bounded p hp σ m)
    (rootResidue_bounded p hp σ (m % N))
  rw [normalDegree_add_c, ← rootDegree_normal, ← rootDegree_normal]
  calc
    m • normalDegree p b σ = (m % N + m / N * N) • normalDegree p b σ := by
      rw [Nat.mul_comm (m / N) N, Nat.mod_add_div]
    _ = (m % N) • normalDegree p b σ + (m / N) • (N • normalDegree p b σ) := by
      rw [add_nsmul, mul_nsmul, smul_comm N (m / N)]
    _ = _ := by rw [hN, mul_smul, natCast_zsmul]

/-- The root equation prevents two distinct residues modulo lcm(p_i) from having the same
signature-residue vector, even when the degree group has torsion. -/
theorem rootResidueVector_injective {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℤ) (σ : Fin n → ℤ) (hroot : IsCanonicalRoot p a (normalDegree p b σ)) :
    Function.Injective (fun m : Fin (signatureLcm p) => rootResidueVector p hp σ m) := by
  intro m k he
  obtain ⟨v, _, hv⟩ := (canonicalRoot_normal_iff p b σ).mp hroot
  have hdiv (i : Fin n) : (p i : ℤ) ∣ (m : ℤ) - (k : ℤ) := by
    have hr := congrArg (fun r => ((r i : Fin (p i)) : ℤ)) he
    simp only [rootResidueVector_cast, rootResidue] at hr
    have hm := Int.emod_add_ediv_mul ((m : ℤ) * σ i) (p i)
    have hk := Int.emod_add_ediv_mul ((k : ℤ) * σ i) (p i)
    refine ⟨((m : ℤ) - (k : ℤ)) * v i - (a : ℤ) *
      (((m : ℤ) * σ i) / (p i) - ((k : ℤ) * σ i) / (p i)), ?_⟩
    nlinarith [hv i]
  have hN : (signatureLcm p : ℤ) ∣ (m : ℤ) - (k : ℤ) := by
    apply Int.natCast_dvd.mpr
    exact Finset.lcm_dvd (fun i _ => Int.natCast_dvd.mp (hdiv i))
  obtain ⟨t, ht⟩ := hN
  have hm := m.isLt
  have hk := k.isLt
  have htz : t = 0 := by
    by_contra h
    have : t ≤ -1 ∨ 1 ≤ t := by omega
    rcases this with ht' | ht' <;> nlinarith
  apply Fin.ext
  simp only [htz, mul_zero, sub_eq_zero] at ht
  exact_mod_cast ht

end CanonicalRoots
