import CanonicalRoots.CoordinateFourierPeriod

noncomputable section
namespace CanonicalRoots

theorem canonical_residue_divisible_period {p a N : ℕ} (hp : 0 < p) (hN : 0 < N)
    (hd : p ∣ N) (σ v : ℤ) (hσ : 0 ≤ σ) (hv : (a : ℤ) * σ + 1 = (p : ℤ) * v)
    (q : ℂ) (hq : q ^ N = 1) (hne : q ≠ 1) :
    -(1 / (N : ℂ)) * (∑ j ∈ Finset.range N, residueFraction p σ j * q ^ j) =
      if q ^ p = 1 then 1 / ((p : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 0 < k := by nlinarith
  simpa only [mul_comm k p] using canonical_residue_common_period hp hk σ v hσ hv q
    (by simpa only [mul_comm k p] using hq) hne

/-- The whole periodic part of the actual root Hilbert formula has the expected
coordinate contributions at every root of a common period. -/
theorem canonicalRoot_periodic_fourier {n a N : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (hN : 0 < N) (hd : ∀ i, p i ∣ N)
    (b : ℤ) (σ : Fin n → ℤ) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsCanonicalRoot p a (normalDegree p b σ))
    (q : ℂ) (hq : q ^ N = 1) (hne : q ≠ 1) :
    -(1 / (N : ℂ)) *
      (∑ j ∈ Finset.range N, (∑ i, residueFraction (p i) (σ i) j) * q ^ j) =
        ∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0 := by
  obtain ⟨v, _, hv⟩ := (canonicalRoot_normal_iff p b σ).mp hroot
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact canonical_residue_divisible_period (hp i) hN (hd i) (σ i) (v i) (hσ i) (hv i) q hq hne

end CanonicalRoots
