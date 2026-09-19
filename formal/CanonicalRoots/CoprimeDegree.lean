import CanonicalRoots.DegreeUniversal
import CanonicalRoots.HigherRealization

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin n → ℕ)

theorem signatureLcm_eq_product (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) :
    signatureLcm p = ∏ i, p i :=
  Finset.lcm_eq_prod (fun _ _ _ _ hij => hcop hij)

/-- Integral degree with product denominator, defined on the actual degree quotient. -/
def productDegree : DegreeGroup p →+ ℤ :=
  degreeLift p (fun i => (productWeights p i : ℤ)) (∏ i, (p i : ℤ)) (fun i => by
    simp only [zsmul_eq_mul, Int.cast_id]
    have h : p i * productWeights p i = ∏ j, p j := by
      simpa only [mul_comm] using productWeights_mul p i
    simpa only [Nat.cast_mul, Nat.cast_prod] using congrArg (fun k : ℕ => (k : ℤ)) h)

@[simp] theorem productDegree_c : productDegree p (cDegree p) = ∏ i, (p i : ℤ) :=
  degreeLift_c p _ _ _

@[simp] theorem productDegree_x (i : Fin n) :
    productDegree p (xDegree p i) = productWeights p i := degreeLift_x p _ _ _ i

@[simp] theorem productDegree_omega :
    productDegree p (omegaDegree p) = (∏ i, (p i : ℤ)) - ∑ i, (productWeights p i : ℤ) := by
  simp only [omegaDegree, map_sub, map_sum, productDegree_c, productDegree_x]

theorem productDegree_eq_zero (hp : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (l : DegreeGroup p) (hl : productDegree p l = 0) : l = 0 := by
  classical
  obtain ⟨b, v, hv, rfl⟩ := degree_normal_exists p hp l
  rw [normalDegree_expression] at hl
  simp only [map_add, map_zsmul, map_sum, productDegree_c, productDegree_x, zsmul_eq_mul, Int.cast_id] at hl
  have hv0 (i : Fin n) : v i = 0 := by
    have hpi : (p i : ℤ) ∣ ∏ j, (p j : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hall : (p i : ℤ) ∣ ∑ j, v j * (productWeights p j : ℤ) := by
      have he : (∑ j, v j * (productWeights p j : ℤ)) = -(b * ∏ j, (p j : ℤ)) := by linarith
      rw [he]
      exact dvd_neg.mpr (dvd_mul_of_dvd_right hpi b)
    have hother : (p i : ℤ) ∣ ∑ j ∈ Finset.univ.erase i, v j * (productWeights p j : ℤ) := by
      apply Finset.dvd_sum
      intro j hj
      have hd : (p i : ℤ) ∣ (productWeights p j : ℤ) := by
        exact_mod_cast signature_dvd_other_weight p (Ne.symm (Finset.mem_erase.mp hj).1)
      exact dvd_mul_of_dvd_right hd (v j)
    have he := Finset.sum_erase_add Finset.univ (fun j => v j * (productWeights p j : ℤ)) (Finset.mem_univ i)
    have hmul : (p i : ℤ) ∣ v i * (productWeights p i : ℤ) := by
      convert dvd_sub hall hother using 1
      omega
    have hdiv := (signature_coprime_weight p hcop i).isCoprime.dvd_of_dvd_mul_right hmul
    have hemod := Int.emod_eq_of_lt (hv i).1 (hv i).2
    rw [Int.emod_eq_zero_of_dvd hdiv] at hemod
    exact hemod.symm
  have hb : b = 0 := by
    simp only [hv0, zero_mul, Finset.sum_const_zero, add_zero] at hl
    exact (mul_eq_zero.mp hl).resolve_right (Finset.prod_ne_zero_iff.mpr (fun i _ => by
      exact_mod_cast ne_of_gt (hp i)))
  rw [normalDegree_expression, hb]
  simp only [hv0, zero_zsmul, Finset.sum_const_zero, add_zero]

theorem productDegree_injective (hp : ∀ i, 0 < p i)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) : Function.Injective (productDegree p) := by
  intro x y h
  apply sub_eq_zero.mp
  apply productDegree_eq_zero p hp hcop
  rw [map_sub, h, sub_self]

end CanonicalRoots
