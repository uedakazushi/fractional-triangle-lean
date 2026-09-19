import CanonicalRoots.RootArithmetic
import CanonicalRoots.GradedRoot

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def productWeights {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, p j

theorem productWeights_mul {n : ℕ} (p : Fin n → ℕ) (i : Fin n) :
    productWeights p i * p i = ∏ j, p j :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem productWeights_pos {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (i : Fin n) :
    0 < productWeights p i := Finset.prod_pos (fun j _ => hp j)

theorem signature_dvd_other_weight {n : ℕ} (p : Fin n → ℕ) {i j : Fin n} (h : i ≠ j) :
    p i ∣ productWeights p j :=
  Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩)

theorem signature_coprime_weight {n : ℕ} (p : Fin n → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) (i : Fin n) :
    Nat.Coprime (p i) (productWeights p i) :=
  Nat.Coprime.prod_right (fun _j hj => hcop (Ne.symm (Finset.mem_erase.mp hj).1))

/-- Independent coprime torsion relations cannot cancel each other in a zero sum. -/
theorem coprime_torsion_sum {G : Type*} [AddCommGroup G] {n : ℕ} (p : Fin n → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (y : Fin n → G) (hy : ∀ i, p i • y i = 0) (hs : ∑ i, y i = 0) (i : Fin n) : y i = 0 := by
  classical
  have hwi : productWeights p i • y i = 0 := by
    have hsum : ∑ j, productWeights p i • y j = productWeights p i • y i := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        obtain ⟨t, ht⟩ := signature_dvd_other_weight p hji
        rw [ht, mul_comm, mul_smul, hy, smul_zero]
      · simp
    rw [Finset.sum_nsmul, hs, smul_zero] at hsum
    exact hsum.symm
  obtain ⟨s, t, hst⟩ := (signature_coprime_weight p hcop i).isCoprime
  calc
    y i = (1 : ℤ) • y i := by simp
    _ = (s * (p i : ℤ) + t * (productWeights p i : ℤ)) • y i := by rw [hst]
    _ = 0 := by simp [add_zsmul, mul_smul, hy, hwi]

theorem productWeights_div {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (i : Fin n) :
    ((∏ j, p j : ℕ) : ℤ) / (p i : ℤ) = (productWeights p i : ℤ) := by
  have h := productWeights_mul p i
  have hi : (p i : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt (hp i)
  have h' : ((∏ j, p j : ℕ) : ℤ) = (productWeights p i : ℤ) * (p i : ℤ) := by
    exact_mod_cast h.symm
  rw [h', Int.mul_ediv_cancel _ hi]

/-- Defect equal to the root index forces R=T for pairwise-coprime signatures. -/
theorem higher_generator_degrees {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 0 < a) (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (i : Fin n) :
    xDegree p i = productWeights p i • τ := by
  let P := ∏ j, p j
  have hP : ∀ j, (p j : ℤ) ∣ (P : ℤ) := fun j => by
    exact_mod_cast Finset.dvd_prod_of_mem p (Finset.mem_univ j)
  have hd : (P : ℤ) • omegaDegree p = (a : ℤ) • cDegree p := by
    rw [denominator_omega p _ hP]
    simp only [P, productWeights_div p hp, hdefect]
  have hcancel := degree_nsmul_injective p hp ha (canonicalRoot_coprime p hp τ hτ)
  have hc : P • τ = cDegree p := by
    apply hcancel
    change a • (P • τ) = a • cDegree p
    rw [smul_comm a P, hτ]
    exact hd
  let y := fun j => xDegree p j - productWeights p j • τ
  have hy : ∀ j, p j • y j = 0 := by
    intro j
    dsimp [y]
    rw [nsmul_sub, ← mul_smul, mul_comm, productWeights_mul, hc]
    have hj := degree_relation p j
    exact sub_eq_zero.mpr hj
  have hs : ∑ j, y j = 0 := by
    have hτ' : (a : ℤ) • τ = cDegree p - ∑ j, xDegree p j := hτ
    have hc' : (P : ℤ) • τ = cDegree p := hc
    have hi : (a : ℤ) • τ = (P : ℤ) • τ - (∑ j, (productWeights p j : ℤ)) • τ := by
      rw [← sub_smul, hdefect]
    rw [hτ', hc'] at hi
    have hsum : ∑ j, xDegree p j = (∑ j, (productWeights p j : ℤ)) • τ := by
      exact sub_right_inj.mp hi
    simp only [y, Finset.sum_sub_distrib]
    rw [hsum]
    have hsum' : ∀ s : Finset (Fin n), (∑ j ∈ s, (productWeights p j : ℤ)) • τ =
        ∑ j ∈ s, productWeights p j • τ := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, add_zsmul, ih]
        simp
    rw [hsum']
    exact sub_self _
  exact sub_eq_zero.mp (coprime_torsion_sum p hcop y hy hs i)

theorem higher_root_eq_top {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 0 < a) (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) : rootSubalgebra p τ = ⊤ :=
  root_eq_top_of_degrees p τ (productWeights p) (higher_generator_degrees p hp ha hcop hdefect τ hτ)

theorem product_defect_coprime {n a : ℕ} (p : Fin n → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a) (i : Fin n) :
    IsCoprime (a : ℤ) (p i : ℤ) := by
  have hP : (p i : ℤ) ∣ ((∏ j, p j : ℕ) : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  have hw : (p i : ℤ) ∣ ∑ j ∈ Finset.univ.erase i, (productWeights p j : ℤ) := by
    apply Finset.dvd_sum
    intro j hj
    exact_mod_cast signature_dvd_other_weight p (Ne.symm (Finset.mem_erase.mp hj).1)
  have hs := Finset.sum_erase_add Finset.univ (fun j => (productWeights p j : ℤ))
    (Finset.mem_univ i)
  have he : (a : ℤ) + (productWeights p i : ℤ) =
      ((∏ j, p j : ℕ) : ℤ) - ∑ j ∈ Finset.univ.erase i, (productWeights p j : ℤ) := by
    omega
  have hdiv : (p i : ℤ) ∣ (a : ℤ) + (productWeights p i : ℤ) := by
    rw [he]
    exact dvd_sub hP hw
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨s, t, hst⟩ := (signature_coprime_weight p hcop i).symm.isCoprime
  refine ⟨-s, t + s * q, ?_⟩
  linear_combination hst - s * hq

/-- Every positive product-defect candidate has a unique actual root in L. -/
theorem higher_root_exists_unique {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 0 < a) (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a) :
    ∃! τ : DegreeGroup p, IsCanonicalRoot p a τ := by
  have hP : ∀ j, (p j : ℤ) ∣ ((∏ j, p j : ℕ) : ℤ) := fun j => by
    exact_mod_cast Finset.dvd_prod_of_mem p (Finset.mem_univ j)
  have hcopP : IsCoprime (a : ℤ) ((∏ j, p j : ℕ) : ℤ) := by
    simpa only [Nat.cast_prod] using
      IsCoprime.prod_right (fun i (_ : i ∈ Finset.univ) => product_defect_coprime p hcop hdefect i)
  have hd : (a : ℤ) ∣ ((∏ j, p j : ℕ) : ℤ) - ∑ i, ((∏ j, p j : ℕ) : ℤ) / (p i : ℤ) := by
    simp only [productWeights_div p hp, hdefect, dvd_refl]
  obtain ⟨τ, hτ⟩ := canonicalRoot_of_index p _ hP hcopP hd
  exact ⟨τ, hτ, fun σ hσ => canonicalRoot_unique p hp ha σ τ hσ hτ⟩

theorem product_defect_admissible {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i)
    (ha : 0 < a)
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a) :
    AdmissibleSignature p := by
  refine ⟨hp, ?_⟩
  let P := ∏ j, p j
  have hP : (0 : ℚ) < P := by
    exact_mod_cast Finset.prod_pos (fun i (_ : i ∈ Finset.univ) => lt_of_lt_of_le (by decide : 0 < 2) (hp i))
  have hwi : ∀ i, (P : ℚ) * ((1 : ℚ) / p i) = (productWeights p i : ℚ) := by
    intro i
    have hmul : (productWeights p i : ℚ) * (p i : ℚ) = P := by
      exact_mod_cast productWeights_mul p i
    have hi : (p i : ℚ) ≠ 0 := by exact_mod_cast (by have := hp i; omega : p i ≠ 0)
    field_simp
    nlinarith
  have hsum : (P : ℚ) * (∑ i, (1 : ℚ) / p i) = ∑ i, (productWeights p i : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hwi i)
  have hd : (P : ℚ) - ∑ i, (productWeights p i : ℚ) = a := by exact_mod_cast hdefect
  have hapos : (0 : ℚ) < a := by exact_mod_cast ha
  nlinarith

/-- Actual graded realization for the coprime product-defect family, before minimality proofs. -/
def higherRootGradedEquiv {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i)
    (ha : 0 < a) (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    GradedAlgEquiv (rootPiece p τ) (presentedPiece (fermat p) (productWeights p)) :=
  rootGradedAmbientEquiv p τ (productWeights p)
    (higher_generator_degrees p (fun i => by have := hp i; omega) ha hcop hdefect τ hτ)
    (root_multiples_injective p (product_defect_admissible p hp ha hdefect) ha τ hτ)

theorem fermat_product_homogeneous {n : ℕ} (p : Fin n → ℕ) :
    IsWeightedHomogeneous (productWeights p) (fermat p) (∏ j, p j) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  have h := (isWeightedHomogeneous_X ℂ (productWeights p) i).pow (p i)
  simpa only [smul_eq_mul, mul_comm (p i), productWeights_mul] using h

theorem fermat_ne_zero {n : ℕ} (hn : 0 < n) (p : Fin n → ℕ) : fermat p ≠ 0 := by
  intro h
  have he := congrArg (eval (fun _ : Fin n => (1 : ℂ))) h
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp [fermat, hnz] at he

theorem fermat_no_constant_or_linear {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i) :
    HasNoConstantOrLinear (fermat p) := by
  classical
  have hp0 : ∀ i, p i ≠ 0 := fun i => by have := hp i; omega
  constructor
  · simp [fermat, coeff_X_pow, hp0]
  · intro i
    have hne : ∀ j, Finsupp.single j (p j) ≠ Finsupp.single i 1 := by
      intro j h
      have he := congrArg (fun d : Fin n →₀ ℕ => d j) h
      by_cases hji : j = i
      · subst j
        simp at he
        have := hp i
        omega
      · simp [Ne.symm hji] at he
        exact hp0 j he
    simp [fermat, coeff_X_pow, hne]

/-- A concrete Fermat presentation of the actual root ring; all fields are proved. -/
def higherRootPresentation {n a : ℕ} (hn : 0 < n) (p : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i)
    (ha : 0 < a) (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) : RootHypersurfacePresentation p τ where
  weights := productWeights p
  weights_pos := productWeights_pos p (fun i => by have := hp i; omega)
  relationDegree := ∏ j, p j
  relationDegree_pos := Finset.prod_pos (fun i _ => by have := hp i; omega)
  polynomial := fermat p
  polynomial_ne_zero := fermat_ne_zero hn p
  homogeneous := fermat_product_homogeneous p
  no_constant_or_linear := fermat_no_constant_or_linear p hp
  isolated := fermat_isolated p hp
  graded_equiv := {
    toAlgEquiv := (higherRootGradedEquiv p hp ha hcop hdefect τ hτ).toAlgEquiv.symm
    preserves := by
      intro m x
      have h := (higherRootGradedEquiv p hp ha hcop hdefect τ hτ).preserves m
        ((higherRootGradedEquiv p hp ha hcop hdefect τ hτ).toAlgEquiv.symm x)
      simpa using h.symm }

/-- Existence of an actual isolated homogeneous hypersurface presentation for the family. -/
theorem higher_root_realization {n a : ℕ} (hn : 0 < n) (p : Fin n → ℕ)
    (hp : ∀ i, 2 ≤ p i) (ha : 0 < a)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (hdefect : ((∏ j, p j : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a) :
    ∃ τ : DegreeGroup p, IsCanonicalRoot p a τ ∧ AdmissibleSignature p ∧
      Nonempty (RootHypersurfacePresentation p τ) := by
  obtain ⟨τ, hτ, hu⟩ := higher_root_exists_unique p (fun i => by have := hp i; omega) ha hcop hdefect
  exact ⟨τ, hτ, product_defect_admissible p hp ha hdefect,
    ⟨higherRootPresentation hn p hp ha hcop hdefect τ hτ⟩⟩

end CanonicalRoots
