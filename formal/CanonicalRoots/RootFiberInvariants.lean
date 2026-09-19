import CanonicalRoots.FiniteFiberAction
import CanonicalRoots.RootPointLocalMap

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)

/-- The original character automorphism as an automorphism over the actual root ring. -/
def ambientRootAlgEquiv (χ : RootCharacter p τ) :
    AmbientRing p ≃ₐ[RootRing p τ] AmbientRing p where
  __ := (ambientCharacterEquiv p τ χ).toRingEquiv
  commutes' r := rootSubalgebra_le_characterFixed p τ r.property χ

@[simp] theorem ambientRootAlgEquiv_toAlgHom (χ : RootCharacter p τ) :
    (ambientRootAlgEquiv p τ χ).toAlgHom = ambientRootAlgHom p τ χ := by
  ext x
  rfl

theorem rootFiberPrime_transitive (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (hτ : IsCanonicalRoot p a τ) (J : Ideal (RootRing p τ))
    (P Q : J.primesOver (AmbientRing p)) :
    ∃ χ : RootCharacter p τ, fiberPrimeEquiv J (ambientRootAlgEquiv p τ χ) P = Q := by
  obtain ⟨χ, hχ⟩ := ambient_primes_over_root_transitive p hp ha τ hτ P.val Q.val
    (P.property.2.over.symm.trans Q.property.2.over)
  exact ⟨χ, Subtype.ext hχ.symm⟩

/-- A globally fixed completed element is determined by its image at any one fiber point. -/
theorem rootCompletedFixed_projection_injective (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (hτ : IsCanonicalRoot p a τ) (J : Ideal (RootRing p τ)) [J.IsMaximal]
    (P : J.primesOver (AmbientRing p)) :
    Function.Injective (fun x : completedRootFixed p τ J => finiteFiberProjection J P x.val) := by
  let : Module.Finite (RootRing p τ) (AmbientRing p) := ambient_finite_over_root p hp ha τ hτ
  intro x y hxy
  apply Subtype.ext
  apply (finiteFiberCompletionEquiv J).injective
  funext Q
  obtain ⟨χ, rfl⟩ := rootFiberPrime_transitive p τ hp ha hτ J P Q
  have hx := finiteFiberCompletionEquiv_equivariant J (ambientRootAlgEquiv p τ χ) P x.val
  have hy := finiteFiberCompletionEquiv_equivariant J (ambientRootAlgEquiv p τ χ) P y.val
  rw [ambientRootAlgEquiv_toAlgHom] at hx hy
  change finiteFiberCompletionEquiv J (completedRootCharacterHom p τ J χ x.val) _ = _ at hx
  change finiteFiberCompletionEquiv J (completedRootCharacterHom p τ J χ y.val) _ = _ at hy
  rw [x.property χ, finiteFiberCompletionEquiv_apply J P] at hx
  rw [y.property χ, finiteFiberCompletionEquiv_apply J P] at hy
  exact hx.trans ((congrArg (fiberCompletionTransport J (ambientRootAlgEquiv p τ χ) P) hxy).trans hy.symm)

end CanonicalRoots
