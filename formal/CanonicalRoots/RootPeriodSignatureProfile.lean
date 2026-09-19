import CanonicalRoots.RootPeriodFourier
import CanonicalRoots.SignatureDivisorRecovery
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section
namespace CanonicalRoots

theorem signatureDivisorProfile_ofFn {n : ℕ} (p : Fin n → ℕ) (e : ℕ) :
    signatureDivisorProfile (List.ofFn p : Multiset ℕ) e =
      ∑ i, if e ∣ p i then (p i : ℚ)⁻¹ else 0 := by
  rw [signatureDivisorProfile_eq_sum]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]

theorem signatureDivisorProfile_ofFn_complex {n : ℕ} (p : Fin n → ℕ) (e : ℕ) :
    (signatureDivisorProfile (List.ofFn p : Multiset ℕ) e : ℂ) =
      ∑ i, if e ∣ p i then (p i : ℂ)⁻¹ else 0 := by
  rw [signatureDivisorProfile_ofFn]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : e ∣ p i <;> simp [hd]

theorem canonicalRoot_periodic_signature_profile {n a N e : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (hN : 0 < N) (hd : ∀ i, p i ∣ N)
    (b : ℤ) (σ : Fin n → ℤ) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsCanonicalRoot p a (normalDegree p b σ))
    (q : ℂ) (hq : IsPrimitiveRoot q e) (he : 2 ≤ e) (heN : e ∣ N) :
    -(1 / (N : ℂ)) *
      (∑ j ∈ Finset.range N, (∑ i, residueFraction (p i) (σ i) j) * q ^ j) =
        (signatureDivisorProfile (List.ofFn p : Multiset ℕ) e : ℂ) / (1 - q ^ (-(a : ℤ))) := by
  rw [canonicalRoot_periodic_fourier p hp hN hd b σ hσ hroot q
    ((hq.pow_eq_one_iff_dvd N).mpr heN) (hq.ne_one (by omega)),
    signatureDivisorProfile_ofFn_complex, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hq.pow_eq_one_iff_dvd]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm]

end CanonicalRoots
