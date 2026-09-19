import CanonicalRoots.CoprimeDegreeEquiv
import CanonicalRoots.CanonicalFiniteFree

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin n → ℕ) (hp : AdmissibleSignature p)
  (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))

include hp hcop in
theorem signatureIndex_eq_productDegree : signatureIndex p = productDegree p (omegaDegree p) := by
  unfold signatureIndex
  rw [signatureLcm_eq_product p hcop, productDegree_omega]
  simp only [Nat.cast_prod]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.cast_prod] using
    productWeights_div p (fun j => lt_of_lt_of_le (by decide) (hp.1 j)) i

include hp ha hτ hcop in
theorem productDegree_canonicalRoot : productDegree p τ = (canonicalRootScale p a : ℤ) := by
  have he := congrArg (productDegree p) hτ
  change productDegree p (a • τ) = productDegree p (omegaDegree p) at he
  rw [map_nsmul, nsmul_eq_mul, ← signatureIndex_eq_productDegree p hp hcop] at he
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hq : signatureIndex p / (a : ℤ) = productDegree p τ := by
    rw [← he, Int.mul_ediv_cancel_left _ ha0]
  change productDegree p τ = ((signatureIndex p / (a : ℤ)).toNat : ℤ)
  rw [Int.toNat_of_nonneg (le_of_lt (canonicalRoot_scale_positive p hp ha τ hτ)), hq]

include hp hcop in
theorem signatureIndex_coprime_coordinate (i : Fin n) : IsCoprime (signatureIndex p) (p i : ℤ) := by
  classical
  rw [signatureIndex_eq_productDegree p hp hcop, productDegree_omega]
  let k : ℤ := (∏ j, (p j : ℤ)) - ∑ j, (productWeights p j : ℤ)
  have hd : (p i : ℤ) ∣ k + productWeights p i := by
    have hP : (p i : ℤ) ∣ ∏ j, (p j : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hother : (p i : ℤ) ∣ ∑ j ∈ Finset.univ.erase i, (productWeights p j : ℤ) := by
      apply Finset.dvd_sum
      intro j hj
      exact_mod_cast signature_dvd_other_weight p (Ne.symm (Finset.mem_erase.mp hj).1)
    have he := Finset.sum_erase_add Finset.univ (fun j => (productWeights p j : ℤ)) (Finset.mem_univ i)
    have hk : k + productWeights p i = (∏ j, (p j : ℤ)) -
        ∑ j ∈ Finset.univ.erase i, (productWeights p j : ℤ) := by
      dsimp [k]
      linarith
    rw [hk]
    exact dvd_sub hP hother
  obtain ⟨t, ht⟩ := hd
  obtain ⟨α, β, hbez⟩ := (signature_coprime_weight p hcop i).symm.isCoprime
  change IsCoprime k (p i : ℤ)
  refine ⟨-α, α * t + β, ?_⟩
  calc
    -α * k + (α * t + β) * (p i : ℤ) =
        α * (productWeights p i : ℤ) + β * (p i : ℤ) := by
      linear_combination -α * ht
    _ = 1 := hbez

include hp ha hτ hcop in
theorem canonicalRootScale_coprime_coordinate (i : Fin n) :
    Nat.Coprime (canonicalRootScale p a) (p i) := by
  have hd : (canonicalRootScale p a : ℤ) ∣ signatureIndex p := by
    refine ⟨a, ?_⟩
    rw [← productDegree_canonicalRoot p hp ha τ hτ hcop, signatureIndex_eq_productDegree p hp hcop]
    have he := congrArg (productDegree p) hτ
    change productDegree p (a • τ) = productDegree p (omegaDegree p) at he
    simpa only [map_nsmul, nsmul_eq_mul, mul_comm] using he.symm
  exact ((signatureIndex_coprime_coordinate p hp hcop i).of_isCoprime_of_dvd_left hd).natCoprime

include hp ha hτ hcop in
theorem canonicalRootScale_coprime_weight (i : Fin n) :
    Nat.Coprime (canonicalRootScale p a) (productWeights p i) :=
  Nat.Coprime.prod_right (fun j _ => canonicalRootScale_coprime_coordinate p hp ha τ hτ hcop j)

include hp ha hτ hcop in
theorem canonicalRoot_eq_multiple_primitive :
    τ = canonicalRootScale p a • coprimePrimitiveDegree p
      (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) hcop := by
  simpa only [productDegree_canonicalRoot p hp ha τ hτ hcop, natCast_zsmul] using
    degree_eq_multiple_primitive p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) hcop τ

theorem productDegree_monomial (d : Fin n →₀ ℕ) :
    productDegree p (Finsupp.weight (xDegree p) d) =
      (Finsupp.weight (productWeights p) d : ℤ) := by
  simp only [Finsupp.weight_eq_sum, map_sum, map_nsmul, productDegree_x,
    nsmul_eq_mul, Nat.cast_id, Nat.cast_sum, Nat.cast_mul]

include hp ha hτ hcop in
theorem monomial_root_degree_iff (d : Fin n →₀ ℕ) :
    (∃ m : ℕ, Finsupp.weight (xDegree p) d = m • τ) ↔
      canonicalRootScale p a ∣ Finsupp.weight (productWeights p) d := by
  constructor
  · rintro ⟨m, hm⟩
    have he := congrArg (productDegree p) hm
    rw [productDegree_monomial, map_nsmul, productDegree_canonicalRoot p hp ha τ hτ hcop,
      nsmul_eq_mul] at he
    refine ⟨m, ?_⟩
    have hnat : Finsupp.weight (productWeights p) d = m * canonicalRootScale p a := by exact_mod_cast he
    simpa only [mul_comm] using hnat
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply productDegree_injective p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) hcop
    rw [productDegree_monomial, map_nsmul, productDegree_canonicalRoot p hp ha τ hτ hcop,
      nsmul_eq_mul, hm, Nat.cast_mul, mul_comm]

include hp ha hτ hcop in
/-- Pure coordinate powers lie on the nonnegative root line precisely at multiples of the root scale. -/
theorem pure_power_root_degree_iff (i : Fin n) (k : ℕ) :
    (∃ m : ℕ, k • xDegree p i = m • τ) ↔ canonicalRootScale p a ∣ k := by
  constructor
  · rintro ⟨m, hm⟩
    have he := congrArg (productDegree p) hm
    simp only [map_nsmul, productDegree_x, productDegree_canonicalRoot p hp ha τ hτ hcop,
      nsmul_eq_mul] at he
    have heN : k * productWeights p i = m * canonicalRootScale p a := by exact_mod_cast he
    have hd : canonicalRootScale p a ∣ k * productWeights p i := by
      rw [heN]
      exact dvd_mul_left _ _
    exact (canonicalRootScale_coprime_weight p hp ha τ hτ hcop i).dvd_of_dvd_mul_right hd
  · rintro ⟨t, rfl⟩
    refine ⟨t * productWeights p i, ?_⟩
    apply productDegree_injective p (fun j => lt_of_lt_of_le (by decide) (hp.1 j)) hcop
    simp only [map_nsmul, productDegree_x, productDegree_canonicalRoot p hp ha τ hτ hcop,
      nsmul_eq_mul, Nat.cast_mul]
    ring

end CanonicalRoots
