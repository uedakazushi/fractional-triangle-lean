import CanonicalRoots.CompletionInvariants
import CanonicalRoots.InvariantExtension

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)

/-- The character action is linear over the actual fixed root ring. -/
def ambientRootLinearAction (χ : RootCharacter p τ) : AmbientRing p →ₗ[RootRing p τ] AmbientRing p where
  toFun := ambientCharacterHom p τ χ
  map_add' := map_add _
  map_smul' r x := by
    change ambientCharacterHom p τ χ ((r : AmbientRing p) * x) =
      (r : AmbientRing p) * ambientCharacterHom p τ χ x
    rw [map_mul, rootSubalgebra_le_characterFixed p τ r.property χ]

def ambientRootRepresentation : Representation (RootRing p τ) (RootCharacter p τ) (AmbientRing p) where
  toFun := ambientRootLinearAction p τ
  map_one' := by
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (ambientCharacterHom_one p τ) x
  map_mul' χ ψ := by
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (ambientCharacterHom_mul p τ χ ψ) x

variable (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

/-- The invariant submodule is the original root ring, including its natural scalar action. -/
def rootInvariantLinearEquiv :
    RootRing p τ ≃ₗ[RootRing p τ] (ambientRootRepresentation p τ).invariants :=
  LinearEquiv.ofBijective
    ((Algebra.linearMap (RootRing p τ) (AmbientRing p)).codRestrict
      (ambientRootRepresentation p τ).invariants
      (fun r χ => rootSubalgebra_le_characterFixed p τ r.property χ)) (by
      constructor
      · intro r s h
        exact Subtype.ext (congrArg
          (fun x : (ambientRootRepresentation p τ).invariants => (x : AmbientRing p)) h)
      · intro x
        have hx : (x : AmbientRing p) ∈ rootSubalgebra p τ := by
          rw [rootSubalgebra_eq_characterFixed p hp ha τ hτ]
          exact x.property
        exact ⟨⟨x, hx⟩, rfl⟩)

@[simp] theorem rootInvariantLinearEquiv_coe (r : RootRing p τ) :
    ((rootInvariantLinearEquiv p τ hp ha hτ r :
      (ambientRootRepresentation p τ).invariants) : AmbientRing p) = r := rfl

variable (I : Ideal (RootRing p τ))

/-- The fixed module after completing along any root-ring ideal is the completed root ring.
The action is on the whole completed finite extension; isolating one point still requires
the decomposition into completed local factors. -/
def rootCompletionEquivFixed :
    AdicCompletion I (RootRing p τ) ≃ₗ[AdicCompletion I (RootRing p τ)]
      (adicRepresentation I (ambientRootRepresentation p τ)).invariants := by
  let : Finite (RootCharacter p τ) := canonicalRootCharacters_finite p hp ha τ hτ
  let : Fintype (RootCharacter p τ) := Fintype.ofFinite _
  let : Invertible (Fintype.card (RootCharacter p τ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let : Invertible (Fintype.card (RootCharacter p τ) : RootRing p τ) := by
    simpa only [map_natCast] using
      Invertible.map (algebraMap ℂ (RootRing p τ)) (Fintype.card (RootCharacter p τ) : ℂ)
  exact (AdicCompletion.congr I (rootInvariantLinearEquiv p τ hp ha hτ)).trans
    (adicInvariantsEquiv I (ambientRootRepresentation p τ))

/-- The equivalence is induced by completing the actual inclusion R → T. -/
theorem rootCompletionEquivFixed_coe (x : AdicCompletion I (RootRing p τ)) :
    ((rootCompletionEquivFixed p τ hp ha hτ I x :
      (adicRepresentation I (ambientRootRepresentation p τ)).invariants) :
      AdicCompletion I (AmbientRing p)) =
      AdicCompletion.map I (Algebra.linearMap (RootRing p τ) (AmbientRing p)) x := by
  change AdicCompletion.map I (ambientRootRepresentation p τ).invariants.subtype
      (AdicCompletion.map I (rootInvariantLinearEquiv p τ hp ha hτ).toLinearMap x) = _
  rw [AdicCompletion.map_comp_apply]
  rfl

include hp ha hτ in
theorem rootCompletedInclusion_injective :
    Function.Injective (AdicCompletion.map I (Algebra.linearMap (RootRing p τ) (AmbientRing p))) := by
  intro x y h
  apply (rootCompletionEquivFixed p τ hp ha hτ I).injective
  apply Subtype.ext
  simpa only [rootCompletionEquivFixed_coe] using h

include hp ha hτ in
/-- Every fixed completed element has one and only one preimage in the root completion. -/
theorem rootCompleted_fixed_iff_exists (x : AdicCompletion I (AmbientRing p)) :
    (∀ χ : RootCharacter p τ, AdicCompletion.map I (ambientRootLinearAction p τ χ) x = x) ↔
      ∃! r : AdicCompletion I (RootRing p τ),
        AdicCompletion.map I (Algebra.linearMap (RootRing p τ) (AmbientRing p)) r = x := by
  constructor
  · intro hx
    have hx' : x ∈ (adicRepresentation I (ambientRootRepresentation p τ)).invariants := hx
    let e := rootCompletionEquivFixed p τ hp ha hτ I
    refine ⟨e.symm ⟨x, hx'⟩, ?_, ?_⟩
    · change AdicCompletion.map I (Algebra.linearMap (RootRing p τ) (AmbientRing p))
        (e.symm ⟨x, hx'⟩) = x
      rw [← rootCompletionEquivFixed_coe p τ hp ha hτ]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx'⟩)
    · intro y hy
      apply e.injective
      apply Subtype.ext
      rw [e.apply_symm_apply]
      simpa only [e, rootCompletionEquivFixed_coe] using hy
  · rintro ⟨r, rfl, _⟩ χ
    rw [← rootCompletionEquivFixed_coe p τ hp ha hτ]
    exact (rootCompletionEquivFixed p τ hp ha hτ I r).property χ

end CanonicalRoots
