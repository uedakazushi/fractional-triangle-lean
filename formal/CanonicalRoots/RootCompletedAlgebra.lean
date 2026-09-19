import CanonicalRoots.RootCompletionInvariants
import CanonicalRoots.AdicAlgebraFunctor

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)

/-- Regard the proved character action as an algebra map over its actual root fixed ring. -/
def ambientRootAlgHom (χ : RootCharacter p τ) : AmbientRing p →ₐ[RootRing p τ] AmbientRing p :=
  AlgHom.ofLinearMap (ambientRootLinearAction p τ χ)
    (map_one (ambientCharacterHom p τ χ)) (map_mul (ambientCharacterHom p τ χ))

theorem ambientRootAlgHom_one : ambientRootAlgHom p τ 1 = AlgHom.id _ _ := by
  apply AlgHom.ext
  intro x
  exact DFunLike.congr_fun (ambientCharacterHom_one p τ) x

theorem ambientRootAlgHom_mul (χ ψ : RootCharacter p τ) :
    ambientRootAlgHom p τ (χ * ψ) = (ambientRootAlgHom p τ χ).comp (ambientRootAlgHom p τ ψ) := by
  apply AlgHom.ext
  intro x
  exact DFunLike.congr_fun (ambientCharacterHom_mul p τ χ ψ) x

variable (I : Ideal (RootRing p τ))

local notation "eI" => adicScalarExtensionEquiv (R := RootRing p τ) (S := AmbientRing p) I

abbrev AmbientRootCompletion :=
  AdicCompletion (I.map (algebraMap (RootRing p τ) (AmbientRing p))) (AmbientRing p)

/-- The character algebra map on the actual ring completion at IT. -/
def completedRootCharacterHom (χ : RootCharacter p τ) :
    AmbientRootCompletion p τ I →ₐ[RootRing p τ] AmbientRootCompletion p τ I :=
  adicAlgebraMap I (ambientRootAlgHom p τ χ)

theorem completedRootCharacterHom_one : completedRootCharacterHom p τ I 1 = AlgHom.id _ _ := by
  rw [completedRootCharacterHom, ambientRootAlgHom_one, adicAlgebraMap_id]
  rfl

theorem completedRootCharacterHom_mul (χ ψ : RootCharacter p τ) :
    completedRootCharacterHom p τ I (χ * ψ) =
      (completedRootCharacterHom p τ I χ).comp (completedRootCharacterHom p τ I ψ) := by
  simp only [completedRootCharacterHom, ambientRootAlgHom_mul, adicAlgebraMap_comp]
  rfl

def completedRootCharacterEquiv (χ : RootCharacter p τ) :
    AmbientRootCompletion p τ I ≃ₐ[RootRing p τ] AmbientRootCompletion p τ I :=
  AlgEquiv.ofAlgHom (completedRootCharacterHom p τ I χ) (completedRootCharacterHom p τ I χ⁻¹)
    (by rw [← completedRootCharacterHom_mul, mul_inv_cancel χ, completedRootCharacterHom_one])
    (by rw [← completedRootCharacterHom_mul, inv_mul_cancel χ, completedRootCharacterHom_one])

/-- The complete finite character group acts by automorphisms on the completed extension. -/
def completedRootCharacterAction :
    RootCharacter p τ →* (AmbientRootCompletion p τ I ≃ₐ[RootRing p τ] AmbientRootCompletion p τ I) where
  toFun := completedRootCharacterEquiv p τ I
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (completedRootCharacterHom_one p τ I) x
  map_mul' χ ψ := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (completedRootCharacterHom_mul p τ I χ ψ) x

theorem completedRootCharacterHom_conjugate (χ : RootCharacter p τ)
    (x : AdicCompletion I (AmbientRing p)) :
    completedRootCharacterHom p τ I χ (eI x) =
      eI (AdicCompletion.map I (ambientRootLinearAction p τ χ) x) := by
  change eI
      (AdicCompletion.map I (ambientRootLinearAction p τ χ)
        ((eI).symm (eI x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The fixed algebra inside the completed finite extension. -/
def completedRootFixed : Subalgebra (RootRing p τ) (AmbientRootCompletion p τ I) where
  carrier := {x | ∀ χ : RootCharacter p τ, completedRootCharacterHom p τ I χ x = x}
  zero_mem' χ := map_zero _
  one_mem' χ := map_one _
  add_mem' hx hy χ := by rw [map_add, hx χ, hy χ]
  mul_mem' hx hy χ := by rw [map_mul, hx χ, hy χ]
  algebraMap_mem' r χ := (completedRootCharacterHom p τ I χ).commutes r

/-- Complete the original R → T inclusion and corestrict to its proved fixed image. -/
def rootCompletedFixedMap : AdicCompletion I (RootRing p τ) →ₐ[RootRing p τ]
    completedRootFixed p τ I :=
  (adicBaseMap I).codRestrict (completedRootFixed p τ I) (fun x χ => by
    exact DFunLike.congr_fun (adicAlgebraMap_comp_base I (ambientRootAlgHom p τ χ)) x)

theorem rootCompletedFixedMap_coe (x : AdicCompletion I (RootRing p τ)) :
    ((rootCompletedFixedMap p τ I x : completedRootFixed p τ I) : AmbientRootCompletion p τ I) =
      eI
        (AdicCompletion.map I (Algebra.linearMap (RootRing p τ) (AmbientRing p)) x) := rfl

variable (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
theorem rootCompletedFixedMap_bijective : Function.Bijective (rootCompletedFixedMap p τ I) := by
  constructor
  · intro x y h
    apply rootCompletedInclusion_injective p τ hp ha hτ I
    apply (eI).injective
    exact congrArg (fun v : completedRootFixed p τ I => (v : AmbientRootCompletion p τ I)) h
  · intro x
    let y : AdicCompletion I (AmbientRing p) := (eI).symm x.val
    have hy : ∀ χ : RootCharacter p τ,
        AdicCompletion.map I (ambientRootLinearAction p τ χ) y = y := by
      intro χ
      apply (eI).injective
      rw [← completedRootCharacterHom_conjugate]
      change completedRootCharacterHom p τ I χ
        (eI ((eI).symm x.val)) = _
      rw [LinearEquiv.apply_symm_apply]
      exact x.property χ
    obtain ⟨r, hr, _⟩ := (rootCompleted_fixed_iff_exists p τ hp ha hτ I y).mp hy
    refine ⟨r, ?_⟩
    apply Subtype.ext
    rw [rootCompletedFixedMap_coe, hr]
    exact (eI).apply_symm_apply x.val

/-- The completion of the root ring is the fixed algebra in the completion of T along IT.
This is an algebra equivalence with no additional invariant or classification hypothesis. -/
def rootCompletedAlgebraEquiv :
    AdicCompletion I (RootRing p τ) ≃ₐ[RootRing p τ] completedRootFixed p τ I :=
  AlgEquiv.ofBijective (rootCompletedFixedMap p τ I)
    (rootCompletedFixedMap_bijective p τ I hp ha hτ)

end CanonicalRoots
