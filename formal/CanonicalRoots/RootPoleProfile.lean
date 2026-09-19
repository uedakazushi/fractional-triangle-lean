import CanonicalRoots.RootPoleComparison
import CanonicalRoots.TargetTernarySupport

noncomputable section
namespace CanonicalRoots

def rootPoleCoefficient {n : ℕ} (p : Fin n → ℕ) (a : ℕ) (q : ℂ) : ℂ :=
  ∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0

/-- Clearing the defect factor is valid even when no signature coordinate
contributes: each nonempty summand supplies its own nonzero-denominator proof. -/
theorem rootPoleCoefficient_mul_defect {n a e : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (q : ℂ) (hq : IsPrimitiveRoot q e) (he : 2 ≤ e) :
    (1 - q ^ (-(a : ℤ))) * rootPoleCoefficient p a q =
      (signatureDivisorProfile (List.ofFn p : Multiset ℕ) e : ℂ) := by
  classical
  obtain ⟨b, σ, hσ, rfl⟩ := degree_normal_exists p hp τ
  rw [rootPoleCoefficient, Finset.mul_sum, signatureDivisorProfile_ofFn_complex]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : e ∣ p i
  · have hqi := (hq.pow_eq_one_iff_dvd (p i)).mpr hd
    have hden := (canonicalRoot_coordinate_fourier p hp b σ (fun i => (hσ i).1)
      hτ i q hqi (hq.ne_one (by omega))).1
    simp only [hqi, hd, ↓reduceIte]
    field_simp
  · simp [hq.pow_eq_one_iff_dvd, hd]

theorem negative_defect_power {a A B C h : ℕ} (q : ℂ) (hq : q ≠ 0)
    (hdef : h = a + (A + B + C)) (hA : q ^ A = 1) (hh : q ^ h = q ^ B) :
    q ^ (-(a : ℤ)) = q ^ C := by
  have he : q ^ a * q ^ C = 1 := by
    apply mul_right_cancel₀ (pow_ne_zero B hq)
    calc
      _ = q ^ h := by rw [hdef, pow_add, pow_add, pow_add, hA]; ring
      _ = _ := by rw [hh, one_mul]
  simpa only [zpow_neg, zpow_natCast] using inv_eq_of_mul_eq_one_right he

theorem root_profile_common_period {n e : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (he : 0 < e) :
    ∃ N : ℕ, 0 < N ∧ (∀ i, p i ∣ N) ∧ e ∣ N := by
  refine ⟨signatureLcm p * e, Nat.mul_pos (signature_lcm_pos p hp) he, ?_, dvd_mul_left _ _⟩
  intro i
  exact dvd_mul_of_dvd_left (signature_dvd_lcm p i) _

/-- The actual signature has no divisor contribution when the primitive root
does not divide any presentation weight. The period is discharged internally. -/
theorem Target.ternary_profile_no_weight {a e : ℕ} (t : Target 3 a) (he : 2 ≤ e)
    (hw : ∀ i, ¬ e ∣ t.presentation.weights i) :
    signatureDivisorProfile (List.ofFn t.signature : Multiset ℕ) e = 0 := by
  classical
  let q : ℂ := Complex.exp (2 * Real.pi * Complex.I / e)
  have hq : IsPrimitiveRoot q e := Complex.isPrimitiveRoot_exp e (by omega)
  have hp : ∀ i, 0 < t.signature i := fun i => by have := t.admissible.1 i; omega
  obtain ⟨N, hN, hd, heN⟩ := root_profile_common_period t.signature hp (by omega : 0 < e)
  have hc := t.presentation.no_weight_pole t.signature t.admissible t.parameter_input
    t.tau t.root_equation hN hd q ((hq.pow_eq_one_iff_dvd N).mpr heN) (hq.ne_one (by omega))
    (fun i hpow => hw i ((hq.pow_eq_one_iff_dvd _).mp hpow))
  have hm := rootPoleCoefficient_mul_defect t.signature hp t.tau t.root_equation q hq he
  change rootPoleCoefficient t.signature a q = 0 at hc
  rw [hc, mul_zero] at hm
  exact_mod_cast hm.symm

/-- The actual signature's divisor profile when exactly two weights are divisible.
The relation-degree divisibility and all common-period hypotheses are derived. -/
theorem Target.ternary_profile_pair_weight {a e : ℕ} (t : Target 3 a) (he : 2 ≤ e)
    (σ : Equiv.Perm (Fin 3)) (hA : e ∣ t.presentation.weights (σ 0))
    (hB : e ∣ t.presentation.weights (σ 1)) (hC : ¬ e ∣ t.presentation.weights (σ 2)) :
    signatureDivisorProfile (List.ofFn t.signature : Multiset ℕ) e =
      (t.presentation.relationDegree : ℚ) /
        ((t.presentation.weights (σ 0) : ℚ) * t.presentation.weights (σ 1)) := by
  classical
  let q : ℂ := Complex.exp (2 * Real.pi * Complex.I / e)
  have hq : IsPrimitiveRoot q e := Complex.isPrimitiveRoot_exp e (by omega)
  have hp : ∀ i, 0 < t.signature i := fun i => by have := t.admissible.1 i; omega
  obtain ⟨N, hN, hd, heN⟩ := root_profile_common_period t.signature hp (by omega : 0 < e)
  have hdegree : e ∣ t.presentation.relationDegree := (Nat.dvd_gcd hA hB).trans
    (t.ternary_pair_weight_gcd_dvd (σ 0) (σ 1) (σ.injective.ne (by decide)))
  have hqA := (hq.pow_eq_one_iff_dvd _).mpr hA
  have hqB := (hq.pow_eq_one_iff_dvd _).mpr hB
  have hqC : q ^ t.presentation.weights (σ 2) ≠ 1 := fun h => hC ((hq.pow_eq_one_iff_dvd _).mp h)
  have hqh := (hq.pow_eq_one_iff_dvd _).mpr hdegree
  have hs : (∑ i, t.presentation.weights i) = t.presentation.weights (σ 0) +
      t.presentation.weights (σ 1) + t.presentation.weights (σ 2) := by
    rw [← Equiv.sum_comp σ t.presentation.weights, Fin.sum_univ_three]
  have hdef := t.relationDegree_eq_add_sum_weights
  rw [hs] at hdef
  have hnegative := negative_defect_power q (hq.ne_zero (by omega)) hdef hqA (hqh.trans hqB.symm)
  have hc := t.presentation.pair_weight_pole t.signature t.admissible t.parameter_input
    t.tau t.root_equation hN hd σ q ((hq.pow_eq_one_iff_dvd N).mpr heN)
    (hq.ne_one (by omega)) hqA hqB hqC hqh
  change rootPoleCoefficient t.signature a q = _ at hc
  have hm := (rootPoleCoefficient_mul_defect t.signature hp t.tau t.root_equation q hq he).symm
  rw [hc, hnegative] at hm
  have hden : 1 - q ^ t.presentation.weights (σ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hqC)
  have heq : (signatureDivisorProfile (List.ofFn t.signature : Multiset ℕ) e : ℂ) =
      (t.presentation.relationDegree : ℂ) /
        ((t.presentation.weights (σ 0) : ℂ) * t.presentation.weights (σ 1)) := by
    rw [hm]
    field_simp
  apply Rat.cast_injective (α := ℂ)
  push_cast
  exact heq

end CanonicalRoots
