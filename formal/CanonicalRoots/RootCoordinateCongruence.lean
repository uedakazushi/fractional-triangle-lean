import CanonicalRoots.DegreeUniversal
import CanonicalRoots.RootArithmetic

noncomputable section
namespace CanonicalRoots

/-- A degree homomorphism annihilating omega also annihilates every actual root,
when its modulus divides one signature entry. -/
theorem root_zmod_map_eq_zero {n a m : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (i : Fin n) (hmi : m ∣ p i)
    (φ : DegreeGroup p →+ ZMod m) (hφ : φ (omegaDegree p) = 0) : φ τ = 0 := by
  have hc : IsCoprime (a : ℤ) (m : ℤ) :=
    (canonicalRoot_coprime p hp τ hτ i).of_isCoprime_of_dvd_right (by exact_mod_cast hmi)
  obtain ⟨u,v,huv⟩ := hc
  have ha : a • φ τ = 0 := by
    rw [← map_nsmul, hτ, hφ]
  have hm : m • φ τ = 0 := by simp [nsmul_eq_mul]
  calc
    φ τ = (1 : ℤ) • φ τ := by simp
    _ = (u * (a : ℤ) + v * (m : ℤ)) • φ τ := by rw [huv]
    _ = 0 := by
      rw [add_zsmul, mul_smul, mul_smul]
      simp only [natCast_zsmul, ha, hm, smul_zero, add_zero]

def coordinateDifferenceDegrees {n : ℕ} (m : ℕ) (i j : Fin n) : Fin n → ZMod m :=
  Pi.single i 1 - Pi.single j 1

theorem coordinateDifferenceDegrees_relation {n m : ℕ} (p : Fin n → ℕ) (i j : Fin n)
    (hi : m ∣ p i) (hj : m ∣ p j) (k : Fin n) :
    (p k : ℤ) • coordinateDifferenceDegrees m i j k = 0 := by
  have hi' : (p i : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hi
  have hj' : (p j : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hj
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [coordinateDifferenceDegrees, Pi.single_apply, hki, hkj, eq_comm,
      zsmul_eq_mul, hi', hj']

def degreeCoordinateDifference {n m : ℕ} (p : Fin n → ℕ) (i j : Fin n)
    (hi : m ∣ p i) (hj : m ∣ p j) : DegreeGroup p →+ ZMod m :=
  degreeLift p (coordinateDifferenceDegrees m i j) 0
    (coordinateDifferenceDegrees_relation p i j hi hj)

theorem degreeCoordinateDifference_omega {n m : ℕ} (p : Fin n → ℕ) (i j : Fin n)
    (hi : m ∣ p i) (hj : m ∣ p j) :
    degreeCoordinateDifference p i j hi hj (omegaDegree p) = 0 := by
  simp [omegaDegree, degreeCoordinateDifference, coordinateDifferenceDegrees,
    Finset.sum_sub_distrib, Pi.single_apply]

theorem degreeCoordinateDifference_weight {n m : ℕ} (p : Fin n → ℕ) (i j : Fin n)
    (hi : m ∣ p i) (hj : m ∣ p j) (d : Fin n →₀ ℕ) :
    degreeCoordinateDifference p i j hi hj (Finsupp.weight (xDegree p) d) =
      (d i : ZMod m) - d j := by
  simp [Finsupp.weight_eq_sum, degreeCoordinateDifference, coordinateDifferenceDegrees,
    nsmul_sub, Finset.sum_sub_distrib, Pi.single_apply, nsmul_eq_mul,
    mul_sub, mul_ite]

/-- Root monomials have congruent exponents at any two signature entries divisible by m. -/
theorem root_monomial_coordinate_congruence {n a m : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (i j : Fin n)
    (hi : m ∣ p i) (hj : m ∣ p j) (d : Fin n →₀ ℕ)
    (hd : ∃ k : ℕ, Finsupp.weight (xDegree p) d = k • τ) : d i % m = d j % m := by
  let φ := degreeCoordinateDifference p i j hi hj
  have hτ0 : φ τ = 0 := root_zmod_map_eq_zero p hp τ hτ i hi φ
    (degreeCoordinateDifference_omega p i j hi hj)
  obtain ⟨k,hk⟩ := hd
  have h := congrArg φ hk
  rw [degreeCoordinateDifference_weight, map_nsmul, hτ0, smul_zero] at h
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (sub_eq_zero.mp h)

theorem congruence_bounded_decomposition {a c m : ℕ} (hc : c < m) (h : a % m = c % m) :
    a = m * (a / m) + c := by
  rw [Nat.mod_eq_of_lt hc] at h
  have := Nat.mod_add_div a m
  omega

end CanonicalRoots
