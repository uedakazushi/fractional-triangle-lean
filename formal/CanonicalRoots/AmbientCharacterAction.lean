import CanonicalRoots.RootDegreeQuotient
import CanonicalRoots.AmbientGrading

noncomputable section
namespace CanonicalRoots

def rootCharacterValue {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (χ : RootCharacter p τ) (l : DegreeGroup p) : ℂ :=
  χ (Multiplicative.ofAdd (rootDegreeQuotientMap p τ l))

@[simp] theorem rootCharacterValue_zero {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (χ : RootCharacter p τ) : rootCharacterValue p τ χ 0 = 1 := by
  simp [rootCharacterValue]

@[simp] theorem rootCharacterValue_add {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (χ : RootCharacter p τ) (l k : DegreeGroup p) :
    rootCharacterValue p τ χ (l + k) =
      rootCharacterValue p τ χ l * rootCharacterValue p τ χ k := by
  unfold rootCharacterValue
  rw [map_add]
  exact congrArg (fun z : ℂˣ => (z : ℂ))
    (χ.map_mul (Multiplicative.ofAdd (rootDegreeQuotientMap p τ l))
      (Multiplicative.ofAdd (rootDegreeQuotientMap p τ k)))

@[simp] theorem rootCharacterValue_one {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (l : DegreeGroup p) : rootCharacterValue p τ 1 l = 1 := rfl

@[simp] theorem rootCharacterValue_mul {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (χ ψ : RootCharacter p τ) (l : DegreeGroup p) :
    rootCharacterValue p τ (χ * ψ) l =
      rootCharacterValue p τ χ l * rootCharacterValue p τ ψ l := rfl

@[simp] theorem rootCharacterValue_nsmul_tau {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (χ : RootCharacter p τ) (m : ℕ) : rootCharacterValue p τ χ (m • τ) = 1 := by
  simp [rootCharacterValue]

section Action
variable {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
local instance : DecidableEq (DegreeGroup p) := Classical.decEq _
local instance : GradedAlgebra (ambientPiece p) := ambientGradedAlgebra p

/-- A character acts on the actual Fermat quotient, using its proved internal grading. -/
def ambientCharacterHom (χ : RootCharacter p τ) : AmbientRing p →ₐ[ℂ] AmbientRing p :=
  (DirectSum.toAlgebra ℂ (fun l => ↥(ambientPiece p l))
    (fun l => rootCharacterValue p τ χ l • (ambientPiece p l).subtype)
    (by change rootCharacterValue p τ χ 0 • (1 : AmbientRing p) = 1; simp)
    (by
      intro i j x y
      change rootCharacterValue p τ χ (i + j) • ((x : AmbientRing p) * y) =
        (rootCharacterValue p τ χ i • (x : AmbientRing p)) *
          (rootCharacterValue p τ χ j • (y : AmbientRing p))
      rw [rootCharacterValue_add, smul_mul_smul])).comp
    (DirectSum.decomposeAlgEquiv (ambientPiece p)).toAlgHom

theorem ambientCharacterHom_of_mem (χ : RootCharacter p τ) (l : DegreeGroup p)
    {x : AmbientRing p} (hx : x ∈ ambientPiece p l) :
    ambientCharacterHom p τ χ x = rootCharacterValue p τ χ l • x := by
  simp [ambientCharacterHom, DirectSum.decompose_of_mem (ambientPiece p) hx,
    DirectSum.toAlgebra, DirectSum.toSemiring]

@[simp] theorem ambientCharacterHom_X (χ : RootCharacter p τ) (i : Fin n) :
    ambientCharacterHom p τ χ (ambientQuotient p (MvPolynomial.X i)) =
      rootCharacterValue p τ χ (xDegree p i) • ambientQuotient p (MvPolynomial.X i) := by
  apply ambientCharacterHom_of_mem
  exact Submodule.mem_map.mpr ⟨MvPolynomial.X i,
    MvPolynomial.isWeightedHomogeneous_X ℂ (xDegree p) i, rfl⟩

theorem ambientCharacterHom_one : ambientCharacterHom p τ 1 = AlgHom.id ℂ (AmbientRing p) := by
  apply AlgHom.toLinearMap_injective
  apply DirectSum.decompose_lhom_ext (ambientPiece p)
  intro l
  ext x
  exact (ambientCharacterHom_of_mem p τ 1 l x.property).trans (by simp)

theorem ambientCharacterHom_mul (χ ψ : RootCharacter p τ) :
    ambientCharacterHom p τ (χ * ψ) =
      (ambientCharacterHom p τ χ).comp (ambientCharacterHom p τ ψ) := by
  apply AlgHom.toLinearMap_injective
  apply DirectSum.decompose_lhom_ext (ambientPiece p)
  intro l
  ext x
  change ambientCharacterHom p τ (χ * ψ) x =
    ambientCharacterHom p τ χ (ambientCharacterHom p τ ψ x)
  rw [ambientCharacterHom_of_mem p τ (χ * ψ) l x.property,
    ambientCharacterHom_of_mem p τ ψ l x.property, map_smul,
    ambientCharacterHom_of_mem p τ χ l x.property, rootCharacterValue_mul,
    smul_smul, mul_comm]

/-- The inverse is the action of the inverse character, so this is an algebra automorphism. -/
def ambientCharacterEquiv (χ : RootCharacter p τ) : AmbientRing p ≃ₐ[ℂ] AmbientRing p :=
  AlgEquiv.ofAlgHom (ambientCharacterHom p τ χ) (ambientCharacterHom p τ χ⁻¹)
    (by rw [← ambientCharacterHom_mul, mul_inv_cancel χ, ambientCharacterHom_one])
    (by rw [← ambientCharacterHom_mul, inv_mul_cancel χ, ambientCharacterHom_one])

@[simp] theorem ambientCharacterEquiv_apply (χ : RootCharacter p τ) (x : AmbientRing p) :
    ambientCharacterEquiv p τ χ x = ambientCharacterHom p τ χ x := rfl

/-- The finite character group acts by actual complex algebra automorphisms. -/
def ambientCharacterAction : RootCharacter p τ →* (AmbientRing p ≃ₐ[ℂ] AmbientRing p) where
  toFun := ambientCharacterEquiv p τ
  map_one' := by ext x; exact DFunLike.congr_fun (ambientCharacterHom_one p τ) x
  map_mul' χ ψ := by ext x; exact DFunLike.congr_fun (ambientCharacterHom_mul p τ χ ψ) x

/-- The fixed subalgebra is defined by equality in the actual quotient ring. -/
def ambientCharacterFixed : Subalgebra ℂ (AmbientRing p) where
  carrier := {x | ∀ χ : RootCharacter p τ, ambientCharacterHom p τ χ x = x}
  algebraMap_mem' c χ := (ambientCharacterHom p τ χ).commutes c
  zero_mem' χ := map_zero _
  one_mem' χ := map_one _
  add_mem' hx hy χ := by rw [map_add, hx χ, hy χ]
  mul_mem' hx hy χ := by rw [map_mul, hx χ, hy χ]

theorem rootSubalgebra_le_characterFixed : rootSubalgebra p τ ≤ ambientCharacterFixed p τ := by
  change rootModule p τ ≤ (ambientCharacterFixed p τ).toSubmodule
  refine iSup_le fun m => ?_
  intro x hx χ
  rw [ambientCharacterHom_of_mem p τ χ (m • τ) hx, rootCharacterValue_nsmul_tau, one_smul]

theorem ambientProjection_characterHom (χ : RootCharacter p τ) (l : DegreeGroup p)
    (x : AmbientRing p) :
    ambientProjection p l (ambientCharacterHom p τ χ x) =
      rootCharacterValue p τ χ l • ambientProjection p l x := by
  have he : (ambientProjection p l).comp (ambientCharacterHom p τ χ).toLinearMap =
      rootCharacterValue p τ χ l • ambientProjection p l := by
    apply DirectSum.decompose_lhom_ext (ambientPiece p)
    intro k
    ext y
    change ambientProjection p l (ambientCharacterHom p τ χ y) =
      rootCharacterValue p τ χ l • ambientProjection p l y
    rw [ambientCharacterHom_of_mem p τ χ k y.property, map_smul,
      ambientProjection_of_mem p l k y.property]
    by_cases h : l = k
    · simp [h]
    · simp [h]
  exact DFunLike.congr_fun he x

theorem ambientProjection_eq_decompose (l : DegreeGroup p) (x : AmbientRing p) :
    ambientProjection p l x = (DirectSum.decompose (ambientPiece p) x l : AmbientRing p) := by
  have he : ambientProjection p l = GradedAlgebra.proj (ambientPiece p) l := by
    apply DirectSum.decompose_lhom_ext (ambientPiece p)
    intro k
    ext y
    change ambientProjection p l y = (DirectSum.decompose (ambientPiece p) y l : AmbientRing p)
    rw [ambientProjection_of_mem p l k y.property]
    by_cases h : l = k
    · subst k
      simp
    · rw [ite_eq_right_iff.mpr (fun he => False.elim (h he)),
        DirectSum.decompose_of_mem_ne (ambientPiece p) y.property (Ne.symm h)]
  exact DFunLike.congr_fun he x

end Action
end CanonicalRoots
