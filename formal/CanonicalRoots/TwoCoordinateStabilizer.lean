import CanonicalRoots.PointStabilizer

noncomputable section
namespace CanonicalRoots

/-- The diagonal tuple acting by ζ and ζ⁻¹ on two coordinates. -/
def twoCoordinateUnits {n : ℕ} (i j : Fin n) (ζ : ℂˣ) (k : Fin n) : ℂˣ :=
  if k = i then ζ else if k = j then ζ⁻¹ else 1

@[simp] theorem twoCoordinateUnits_left {n : ℕ} (i j : Fin n) (ζ : ℂˣ) :
    twoCoordinateUnits i j ζ i = ζ := by simp [twoCoordinateUnits]

@[simp] theorem twoCoordinateUnits_right {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ζ : ℂˣ) :
    twoCoordinateUnits i j ζ j = ζ⁻¹ := by simp [twoCoordinateUnits, Ne.symm hij]

@[simp] theorem twoCoordinateUnits_other {n : ℕ} (i j : Fin n) (ζ : ℂˣ) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) : twoCoordinateUnits i j ζ k = 1 := by
  simp [twoCoordinateUnits, hki, hkj]

theorem twoCoordinateUnits_prod {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ζ : ℂˣ) :
    ∏ k, twoCoordinateUnits i j ζ k = 1 := by
  rw [Finset.prod_eq_mul_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij
    (fun k _ hk => twoCoordinateUnits_other i j ζ k hk.1 hk.2)]
  simp [hij]

theorem twoCoordinateUnits_powers {n : ℕ} (p : Fin n → ℕ) (i j : Fin n)
    (ζ : ℂˣ) (hζ : ζ ^ Nat.gcd (p i) (p j) = 1) :
    ∀ k, twoCoordinateUnits i j ζ k ^ p k = 1 := by
  have hi : ζ ^ p i = 1 := orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_iff_pow_eq_one.mpr hζ).trans (Nat.gcd_dvd_left _ _))
  have hj : ζ ^ p j = 1 := orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_iff_pow_eq_one.mpr hζ).trans (Nat.gcd_dvd_right _ _))
  intro k
  by_cases hki : k = i
  · subst k; simpa using hi
  · by_cases hkj : k = j
    · subst k; simp [twoCoordinateUnits, hki, inv_pow, hj]
    · simp [twoCoordinateUnits, hki, hkj]

/-- Every gcd-th root of unity gives a genuine character of L/Zτ, independently of u. -/
def twoCoordinateCharacter {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (i j : Fin (n + 1)) (hij : i ≠ j)
    (ζ : ℂˣ) (hζ : ζ ^ Nat.gcd (p i) (p j) = 1) : RootCharacter p τ :=
  rootCharacterOfCoordinates p hp ha τ hτ (twoCoordinateUnits i j ζ) 1
    (twoCoordinateUnits_powers p i j ζ hζ) (twoCoordinateUnits_prod i j hij ζ) (one_pow _)

@[simp] theorem twoCoordinateCharacter_degree_x {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (i j : Fin (n + 1)) (hij : i ≠ j)
    (ζ : ℂˣ) (hζ : ζ ^ Nat.gcd (p i) (p j) = 1) (k : Fin (n + 1)) :
    rootCharacterDegree p τ (twoCoordinateCharacter p hp ha τ hτ i j hij ζ hζ) (xDegree p k) =
      Additive.ofMul (twoCoordinateUnits i j ζ k) :=
  degreeCharacterOfCoordinates_x p (twoCoordinateUnits i j ζ) 1
    (twoCoordinateUnits_powers p i j ζ hζ) k

theorem twoCoordinateCharacter_mem_stabilizer {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (i j : Fin (n + 1)) (hij : i ≠ j)
    (ζ : ℂˣ) (hζ : ζ ^ Nat.gcd (p i) (p j) = 1) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (hi : z (ambientQuotient p (MvPolynomial.X i)) = 0)
    (hj : z (ambientQuotient p (MvPolynomial.X j)) = 0) :
    twoCoordinateCharacter p hp ha τ hτ i j hij ζ hζ ∈ rootPointStabilizer p τ z := by
  rw [mem_rootPointStabilizer_iff_nonzero]
  intro k hk
  rw [twoCoordinateCharacter_degree_x,
    twoCoordinateUnits_other i j ζ k (by rintro rfl; exact hk hi) (by rintro rfl; exact hk hj)]
  rfl

/-- A point with precisely two zero coordinates has no further stabilizer eigenvalues. -/
theorem twoCoordinateStabilizer_shape {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (_hp : AdmissibleSignature p) (_ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (i j k : Fin (n + 1)) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (hz : ∀ l, l ≠ i → l ≠ j → z (ambientQuotient p (MvPolynomial.X l)) ≠ 0)
    (χ : RootCharacter p τ) (hχ : χ ∈ rootPointStabilizer p τ z) :
    let f := rootCharacterDegree p τ χ
    f (cDegree p) = 0 ∧
    f (xDegree p j) = -f (xDegree p i) ∧
    ((f (xDegree p i)).toMul) ^ Nat.gcd (p i) (p j) = 1 ∧
    ∀ l, l ≠ i → l ≠ j → f (xDegree p l) = 0 := by
  dsimp only
  let f := rootCharacterDegree p τ χ
  have hr (l) (hli : l ≠ i) (hlj : l ≠ j) : f (xDegree p l) = 0 :=
    (mem_rootPointStabilizer_iff_nonzero p τ z χ).mp hχ l (hz l hli hlj)
  have hc : f (cDegree p) = 0 := by
    rw [← degree_relation p k, map_zsmul, hr k hki hkj, zsmul_zero]
  have hs : f (xDegree p i) + f (xDegree p j) = 0 := by
    have he : f (cDegree p) - ∑ l, f (xDegree p l) = 0 := by
      rw [← map_sum, ← map_sub, ← omegaDegree, ← hτ, map_nsmul]
      change a • rootCharacterDegree p τ χ τ = 0
      rw [rootCharacterDegree_tau, nsmul_zero]
    rw [hc, Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij
      (fun l _ hl => hr l hl.1 hl.2), zero_sub, neg_eq_zero] at he
    exact he
  have hj : f (xDegree p j) = -f (xDegree p i) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hs)
  have hpi : p i • f (xDegree p i) = 0 := by
    rw [← map_nsmul, ← natCast_zsmul, degree_relation, hc]
  have hpj : p j • f (xDegree p i) = 0 := by
    have he := congrArg f (degree_relation p j)
    rw [map_zsmul, natCast_zsmul, hj, smul_neg (p j) (f (xDegree p i)), hc, neg_eq_zero] at he
    exact he
  have hg : Nat.gcd (p i) (p j) • f (xDegree p i) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_gcd
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpi) (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpj))
  exact ⟨hc, hj, congrArg Additive.toMul hg, hr⟩

/-- The stabilizer of the actual point is exactly μ_gcd, as a group, not merely a subgroup bound. -/
def twoCoordinateStabilizerEquiv {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (i j k : Fin (n + 1)) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (hi : z (ambientQuotient p (MvPolynomial.X i)) = 0)
    (hj : z (ambientQuotient p (MvPolynomial.X j)) = 0)
    (hz : ∀ l, l ≠ i → l ≠ j → z (ambientQuotient p (MvPolynomial.X l)) ≠ 0) :
    rootPointStabilizer p τ z ≃* rootsOfUnity (Nat.gcd (p i) (p j)) ℂ where
  toFun χ := ⟨(rootCharacterDegree p τ χ.val (xDegree p i)).toMul,
    (mem_rootsOfUnity _ _).mpr
      (twoCoordinateStabilizer_shape p hp ha τ hτ i j k hij hki hkj z hz χ.val χ.property).2.2.1⟩
  invFun ζ := ⟨twoCoordinateCharacter p hp ha τ hτ i j hij ζ.val
    ((mem_rootsOfUnity _ _).mp ζ.property),
    twoCoordinateCharacter_mem_stabilizer p hp ha τ hτ i j hij ζ.val
      ((mem_rootsOfUnity _ _).mp ζ.property) z hi hj⟩
  left_inv χ := by
    apply Subtype.ext
    have hs := twoCoordinateStabilizer_shape p hp ha τ hτ i j k hij hki hkj z hz χ.val χ.property
    apply rootCharacter_ext p (fun l => lt_of_lt_of_le (by decide) (hp.1 l)) τ
    · calc
        rootCharacterDegree p τ
            (twoCoordinateCharacter p hp ha τ hτ i j hij
              (rootCharacterDegree p τ χ.val (xDegree p i)).toMul hs.2.2.1) (cDegree p) = 0 :=
          degreeCharacterOfCoordinates_c p _ 1
            (twoCoordinateUnits_powers p i j _ hs.2.2.1)
        _ = _ := hs.1.symm
    · intro l
      rw [twoCoordinateCharacter_degree_x]
      by_cases hli : l = i
      · subst l
        rw [twoCoordinateUnits_left, ofMul_toMul]
      · by_cases hlj : l = j
        · subst l
          rw [twoCoordinateUnits_right i j hij]
          exact hs.2.1.symm
        · rw [twoCoordinateUnits_other i j _ l hli hlj]
          exact (hs.2.2.2 l hli hlj).symm
  right_inv ζ := by
    apply Subtype.ext
    change (rootCharacterDegree p τ _ (xDegree p i)).toMul = ζ.val
    rw [twoCoordinateCharacter_degree_x, twoCoordinateUnits_left, toMul_ofMul]
  map_mul' χ ψ := by apply Subtype.ext; rfl

theorem twoCoordinateStabilizer_card {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (i j k : Fin (n + 1)) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (hi : z (ambientQuotient p (MvPolynomial.X i)) = 0)
    (hj : z (ambientQuotient p (MvPolynomial.X j)) = 0)
    (hz : ∀ l, l ≠ i → l ≠ j → z (ambientQuotient p (MvPolynomial.X l)) ≠ 0) :
    Nat.card (rootPointStabilizer p τ z) = Nat.gcd (p i) (p j) := by
  let : NeZero (Nat.gcd (p i) (p j)) := ⟨by
    intro he
    have hi0 := (Nat.gcd_eq_zero_iff.mp he).1
    have := hp.1 i
    omega⟩
  exact (Nat.card_congr (twoCoordinateStabilizerEquiv p hp ha τ hτ i j k hij hki hkj z
    hi hj hz).toEquiv).trans (Complex.card_rootsOfUnity _)

end CanonicalRoots
