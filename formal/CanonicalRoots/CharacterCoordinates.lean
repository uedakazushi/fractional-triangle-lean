import CanonicalRoots.RootInvariants

noncomputable section
namespace CanonicalRoots

/-- Pull a quotient character back to the original, torsion-retaining degree group. -/
def rootCharacterDegree {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (χ : RootCharacter p τ) : DegreeGroup p →+ Additive ℂˣ :=
  χ.toAdditiveRight.comp (rootDegreeQuotientMap p τ)

@[simp] theorem rootCharacterDegree_tau {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (χ : RootCharacter p τ) : rootCharacterDegree p τ χ τ = 0 := by
  simp [rootCharacterDegree]

/-- Every actual quotient character satisfies the stated diagonal coordinate equations. -/
theorem rootCharacter_coordinate_equations {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (χ : RootCharacter p τ) :
    let α := fun i => (rootCharacterDegree p τ χ (xDegree p i)).toMul
    let ρ := (rootCharacterDegree p τ χ (cDegree p)).toMul
    (∀ i, α i ^ p i = ρ) ∧ ∏ i, α i = ρ ∧ ρ ^ canonicalRootScale p a = 1 := by
  dsimp only
  let f := rootCharacterDegree p τ χ
  have hft : f τ = 0 := rootCharacterDegree_tau p τ χ
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (f (xDegree p i)).toMul ^ p i = (f (cDegree p)).toMul
    have he := congrArg f (degree_relation p i)
    rw [map_zsmul, natCast_zsmul] at he
    exact congrArg Additive.toMul he
  · have he : f (cDegree p) - ∑ i, f (xDegree p i) = 0 := by
      rw [← map_sum, ← map_sub, ← omegaDegree, ← hτ, map_nsmul, hft, nsmul_zero]
    exact congrArg Additive.toMul (sub_eq_zero.mp he).symm
  · have he : canonicalRootScale p a • f (cDegree p) = 0 := by
      have hN : signatureLcm p • τ = canonicalRootScale p a • cDegree p :=
        canonicalRoot_nat_denominator p hp ha τ hτ
      rw [← map_nsmul, ← hN,
        map_nsmul, hft, nsmul_zero]
    exact congrArg Additive.toMul he

theorem rootCharacter_ext {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) {χ ψ : RootCharacter p τ}
    (hc : rootCharacterDegree p τ χ (cDegree p) = rootCharacterDegree p τ ψ (cDegree p))
    (hx : ∀ i, rootCharacterDegree p τ χ (xDegree p i) =
      rootCharacterDegree p τ ψ (xDegree p i)) : χ = ψ := by
  have he : rootCharacterDegree p τ χ = rootCharacterDegree p τ ψ := by
    apply AddMonoidHom.ext
    intro l
    obtain ⟨b, σ, _, rfl⟩ := degree_normal_exists p hp l
    simp only [normalDegree_expression, map_add, map_zsmul, map_sum, hc, hx]
  apply MonoidHom.ext
  intro z
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples τ) z.toAdd
  have hv := congrArg Additive.toMul (DFunLike.congr_fun he l)
  change χ (Multiplicative.ofAdd (rootDegreeQuotientMap p τ l)) =
    ψ (Multiplicative.ofAdd (rootDegreeQuotientMap p τ l)) at hv
  change rootDegreeQuotientMap p τ l = z.toAdd at hl
  rw [hl] at hv
  exact hv

/-- Evaluate integral free degrees in a prescribed tuple of complex units. -/
def freeDegreeCharacter {n : ℕ} (α : Fin n → ℂˣ) (ρ : ℂˣ) :
    FreeDegrees n →+ Additive ℂˣ where
  toFun v := v none • Additive.ofMul ρ + ∑ i, v (some i) • Additive.ofMul (α i)
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]; abel

@[simp] theorem freeDegreeCharacter_c {n : ℕ} (α : Fin n → ℂˣ) (ρ : ℂˣ) :
    freeDegreeCharacter α ρ (Pi.single none 1) = Additive.ofMul ρ := by
  simp [freeDegreeCharacter]

@[simp] theorem freeDegreeCharacter_x {n : ℕ} (α : Fin n → ℂˣ) (ρ : ℂˣ) (i : Fin n) :
    freeDegreeCharacter α ρ (Pi.single (some i) 1) = Additive.ofMul (α i) := by
  classical
  simp [freeDegreeCharacter, Pi.single_apply, eq_comm]

/-- The tuple descends through exactly the original degree relations. -/
def degreeCharacterOfCoordinates {n : ℕ} (p : Fin n → ℕ)
    (α : Fin n → ℂˣ) (ρ : ℂˣ) (hα : ∀ i, α i ^ p i = ρ) :
    DegreeGroup p →+ Additive ℂˣ :=
  QuotientAddGroup.lift (degreeRelations p) (freeDegreeCharacter α ρ) (by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change freeDegreeCharacter α ρ _ = 0
    rw [map_sub, map_zsmul, freeDegreeCharacter_x, freeDegreeCharacter_c, sub_eq_zero]
    change Additive.ofMul (α i ^ (p i : ℤ)) = Additive.ofMul ρ
    rw [zpow_natCast, hα i])

@[simp] theorem degreeCharacterOfCoordinates_c {n : ℕ} (p : Fin n → ℕ)
    (α : Fin n → ℂˣ) (ρ : ℂˣ) (hα : ∀ i, α i ^ p i = ρ) :
    degreeCharacterOfCoordinates p α ρ hα (cDegree p) = Additive.ofMul ρ :=
  freeDegreeCharacter_c α ρ

@[simp] theorem degreeCharacterOfCoordinates_x {n : ℕ} (p : Fin n → ℕ)
    (α : Fin n → ℂˣ) (ρ : ℂˣ) (hα : ∀ i, α i ^ p i = ρ) (i : Fin n) :
    degreeCharacterOfCoordinates p α ρ hα (xDegree p i) = Additive.ofMul (α i) :=
  freeDegreeCharacter_x α ρ i

/-- The canonical-root equations force the tuple character to kill τ. -/
theorem degreeCharacterOfCoordinates_tau {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (α : Fin (n + 1) → ℂˣ) (ρ : ℂˣ)
    (hα : ∀ i, α i ^ p i = ρ) (hprod : ∏ i, α i = ρ)
    (hρ : ρ ^ canonicalRootScale p a = 1) :
    degreeCharacterOfCoordinates p α ρ hα τ = 0 := by
  let f := degreeCharacterOfCoordinates p α ρ hα
  have hfa : a • f τ = 0 := by
    rw [← map_nsmul, hτ, omegaDegree, map_sub, map_sum]
    simp only [f, degreeCharacterOfCoordinates_c, degreeCharacterOfCoordinates_x]
    change Additive.ofMul ρ - Additive.ofMul (∏ i, α i) = 0
    rw [hprod, sub_self]
  have hfN : signatureLcm p • f τ = 0 := by
    rw [← map_nsmul, canonicalRoot_nat_denominator p hp ha τ hτ, map_nsmul]
    dsimp only [f]
    rw [degreeCharacterOfCoordinates_c]
    change Additive.ofMul (ρ ^ canonicalRootScale p a) = 0
    rw [hρ]
    rfl
  have hcop := canonicalRoot_coprime_lcm p
    (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ hτ
  have hd : addOrderOf (f τ) ∣ 1 := by
    have hg := Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hfa)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hfN)
    simpa only [hcop.gcd_eq_one] using hg
  have hz := addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
  simpa only [one_nsmul] using hz

/-- Coordinates satisfying the group equations give a character of L/Zτ. -/
def rootCharacterOfCoordinates {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (α : Fin (n + 1) → ℂˣ) (ρ : ℂˣ)
    (hα : ∀ i, α i ^ p i = ρ) (hprod : ∏ i, α i = ρ)
    (hρ : ρ ^ canonicalRootScale p a = 1) : RootCharacter p τ :=
  (QuotientAddGroup.lift (AddSubgroup.zmultiples τ)
    (degreeCharacterOfCoordinates p α ρ hα) (by
      rw [AddSubgroup.zmultiples_le]
      exact degreeCharacterOfCoordinates_tau p hp ha τ hτ α ρ hα hprod hρ)).toMultiplicativeLeft

@[simp] theorem rootCharacterOfCoordinates_apply {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (α : Fin (n + 1) → ℂˣ) (ρ : ℂˣ)
    (hα : ∀ i, α i ^ p i = ρ) (hprod : ∏ i, α i = ρ)
    (hρ : ρ ^ canonicalRootScale p a = 1) (l : DegreeGroup p) :
    rootCharacterOfCoordinates p hp ha τ hτ α ρ hα hprod hρ
      (Multiplicative.ofAdd (rootDegreeQuotientMap p τ l)) =
      Additive.toMul (degreeCharacterOfCoordinates p α ρ hα l) := rfl

/-- An exact coordinate description, including the converse existence direction. -/
theorem rootCharacter_coordinates_iff {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (α : Fin (n + 1) → ℂˣ) (ρ : ℂˣ) :
    (∃ χ : RootCharacter p τ,
      (∀ i, rootCharacterDegree p τ χ (xDegree p i) = Additive.ofMul (α i)) ∧
      rootCharacterDegree p τ χ (cDegree p) = Additive.ofMul ρ) ↔
      (∀ i, α i ^ p i = ρ) ∧ ∏ i, α i = ρ ∧ ρ ^ canonicalRootScale p a = 1 := by
  constructor
  · rintro ⟨χ, hx, hc⟩
    simpa only [hx, hc, Additive.toMul, Equiv.symm_apply_apply] using
      rootCharacter_coordinate_equations p hp ha τ hτ χ
  · rintro ⟨hα, hprod, hρ⟩
    refine ⟨rootCharacterOfCoordinates p hp ha τ hτ α ρ hα hprod hρ, ?_, ?_⟩
    · intro i
      exact degreeCharacterOfCoordinates_x p α ρ hα i
    · exact degreeCharacterOfCoordinates_c p α ρ hα

end CanonicalRoots
