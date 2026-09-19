import CanonicalRoots.CharacterCoordinates

noncomputable section
namespace CanonicalRoots

/-- The stabilizer of an actual complex-valued point of the Fermat quotient. -/
def rootPointStabilizer {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) : Subgroup (RootCharacter p τ) where
  carrier := {χ | z.comp (ambientCharacterHom p τ χ) = z}
  one_mem' := by
    change z.comp (ambientCharacterHom p τ 1) = z
    rw [ambientCharacterHom_one]; rfl
  mul_mem' {χ ψ} hχ hψ := by
    change z.comp (ambientCharacterHom p τ (χ * ψ)) = z
    rw [ambientCharacterHom_mul, ← AlgHom.comp_assoc, hχ, hψ]
  inv_mem' {χ} hχ := by
    have he := congrArg (fun f : AmbientRing p →ₐ[ℂ] ℂ =>
      f.comp (ambientCharacterHom p τ χ⁻¹)) hχ
    rw [AlgHom.comp_assoc, ← ambientCharacterHom_mul, mul_inv_cancel χ,
      ambientCharacterHom_one, AlgHom.comp_id] at he
    exact he.symm

/-- Stabilizing the quotient point is exactly stabilizing all coordinate values. -/
theorem mem_rootPointStabilizer_iff_coordinates {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) (χ : RootCharacter p τ) :
    χ ∈ rootPointStabilizer p τ z ↔ ∀ i,
      rootCharacterValue p τ χ (xDegree p i) * z (ambientQuotient p (MvPolynomial.X i)) =
        z (ambientQuotient p (MvPolynomial.X i)) := by
  constructor
  · intro h i
    have he := DFunLike.congr_fun h (ambientQuotient p (MvPolynomial.X i))
    change z (ambientCharacterHom p τ χ (ambientQuotient p (MvPolynomial.X i))) = _ at he
    simpa only [ambientCharacterHom_X, map_smul, smul_eq_mul] using he
  · intro h
    change z.comp (ambientCharacterHom p τ χ) = z
    have he : (z.comp (ambientCharacterHom p τ χ)).comp (ambientQuotient p) =
        z.comp (ambientQuotient p) := by
      apply MvPolynomial.algHom_ext
      intro i
      change z (ambientCharacterHom p τ χ (ambientQuotient p (MvPolynomial.X i))) = _
      simpa only [ambientCharacterHom_X, map_smul, smul_eq_mul, AlgHom.comp_apply] using h i
    apply AlgHom.ext
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (fermatIdeal p) x
    exact DFunLike.congr_fun he f

/-- Zero coordinates impose no stabilizer condition; every nonzero coordinate forces eigenvalue 1. -/
theorem mem_rootPointStabilizer_iff_nonzero {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (z : AmbientRing p →ₐ[ℂ] ℂ) (χ : RootCharacter p τ) :
    χ ∈ rootPointStabilizer p τ z ↔ ∀ i,
      z (ambientQuotient p (MvPolynomial.X i)) ≠ 0 →
        rootCharacterDegree p τ χ (xDegree p i) = 0 := by
  rw [mem_rootPointStabilizer_iff_coordinates]
  constructor
  · intro h i hi
    have he : rootCharacterValue p τ χ (xDegree p i) = 1 :=
      mul_right_cancel₀ hi ((h i).trans (one_mul _).symm)
    exact congrArg Additive.ofMul (Units.ext he)
  · intro h i
    by_cases hi : z (ambientQuotient p (MvPolynomial.X i)) = 0
    · rw [hi, mul_zero]
    · have he : rootCharacterValue p τ χ (xDegree p i) = 1 :=
        congrArg (fun v : Additive ℂˣ => (v.toMul : ℂ)) (h i hi)
      rw [he, one_mul]

end CanonicalRoots
