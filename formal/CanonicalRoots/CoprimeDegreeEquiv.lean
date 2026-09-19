import CanonicalRoots.CoprimeDegree

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin n → ℕ)
  (hp : ∀ i, 0 < p i) (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))

include hcop in
theorem productDegree_one_exists : ∃ l : DegreeGroup p, productDegree p l = 1 := by
  classical
  have hbez (i : Fin n) : ∃ α β : ℤ,
      α * (productWeights p i : ℤ) + β * (p i : ℤ) = 1 :=
    (signature_coprime_weight p hcop i).symm.isCoprime
  choose α β hα using hbez
  let S : ℤ := ∑ j, α j * (productWeights p j : ℤ)
  have hi (i : Fin n) : (p i : ℤ) ∣ S - 1 := by
    have hother : (p i : ℤ) ∣ ∑ j ∈ Finset.univ.erase i, α j * (productWeights p j : ℤ) := by
      apply Finset.dvd_sum
      intro j hj
      have hd : (p i : ℤ) ∣ (productWeights p j : ℤ) := by
        exact_mod_cast signature_dvd_other_weight p (Ne.symm (Finset.mem_erase.mp hj).1)
      exact dvd_mul_of_dvd_right hd (α j)
    have he := Finset.sum_erase_add Finset.univ (fun j => α j * (productWeights p j : ℤ)) (Finset.mem_univ i)
    have hs : S - 1 = (∑ j ∈ Finset.univ.erase i, α j * (productWeights p j : ℤ)) - β i * p i := by
      dsimp [S]
      linarith [hα i]
    rw [hs]
    exact dvd_sub hother (dvd_mul_left _ _)
  have hP : (∏ i, (p i : ℤ)) ∣ S - 1 :=
    Fintype.prod_dvd_of_coprime (fun _ _ hij => (hcop hij).isCoprime) hi
  obtain ⟨c, hc⟩ := hP
  refine ⟨(∑ i, α i • xDegree p i) - c • cDegree p, ?_⟩
  simp only [map_sub, map_sum, map_zsmul, productDegree_x, productDegree_c, zsmul_eq_mul, Int.cast_id]
  change S - c * (∏ i, (p i : ℤ)) = 1
  linarith

include hcop in
theorem productDegree_surjective : Function.Surjective (productDegree p) := by
  obtain ⟨l, hl⟩ := productDegree_one_exists p hcop
  intro k
  exact ⟨k • l, by simp only [map_zsmul, hl, zsmul_eq_mul, Int.cast_id, mul_one]⟩

/-- Pairwise coprimality makes the original degree group exactly Z, without quotienting out torsion. -/
def coprimeDegreeEquiv : DegreeGroup p ≃+ ℤ :=
  AddEquiv.ofBijective (productDegree p)
    ⟨productDegree_injective p hp hcop, productDegree_surjective p hcop⟩

def coprimePrimitiveDegree : DegreeGroup p := (coprimeDegreeEquiv p hp hcop).symm 1

@[simp] theorem productDegree_primitive :
    productDegree p (coprimePrimitiveDegree p hp hcop) = 1 :=
  (coprimeDegreeEquiv p hp hcop).apply_symm_apply 1

theorem degree_eq_multiple_primitive (l : DegreeGroup p) :
    l = productDegree p l • coprimePrimitiveDegree p hp hcop := by
  apply productDegree_injective p hp hcop
  simp only [map_zsmul, productDegree_primitive, zsmul_eq_mul, Int.cast_id, mul_one]

theorem xDegree_eq_multiple_primitive (i : Fin n) :
    xDegree p i = (productWeights p i : ℤ) • coprimePrimitiveDegree p hp hcop := by
  simpa only [productDegree_x] using degree_eq_multiple_primitive p hp hcop (xDegree p i)

end CanonicalRoots
