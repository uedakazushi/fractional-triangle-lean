import CanonicalRoots.RootCompletionInvariants
import CanonicalRoots.RootPointLocalMap

noncomputable section
namespace CanonicalRoots.CompletionInvariantTests

/-- Complete at the actual image of an arbitrary complex point, not a formal placeholder ideal. -/
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (z : AmbientRing p →ₐ[ℂ] ℂ)
    (x : AdicCompletion (RingHom.ker (rootPoint p τ z).toRingHom) (AmbientRing p)) :
    (∀ χ : RootCharacter p τ,
      AdicCompletion.map (RingHom.ker (rootPoint p τ z).toRingHom)
        (ambientRootLinearAction p τ χ) x = x) ↔
      ∃! r : AdicCompletion (RingHom.ker (rootPoint p τ z).toRingHom) (RootRing p τ),
        AdicCompletion.map (RingHom.ker (rootPoint p τ z).toRingHom)
          (Algebra.linearMap (RootRing p τ) (AmbientRing p)) r = x :=
  rootCompleted_fixed_iff_exists p τ hp ha hτ _ x

/-- The generic completion theorem does not require Noetherianity or a finite module. -/
example {R G M : Type*} [CommRing R] [Group G] [Fintype G]
    [Invertible (Fintype.card G : R)] [AddCommGroup M] [Module R M]
    (I : Ideal R) (ρ : Representation R G M) :
    Nonempty (AdicCompletion I ρ.invariants ≃ₗ[AdicCompletion I R]
      (adicRepresentation I ρ).invariants) := ⟨adicInvariantsEquiv I ρ⟩

end CanonicalRoots.CompletionInvariantTests

#check CanonicalRoots.rootCompletionEquivFixed
#check CanonicalRoots.rootCompleted_fixed_iff_exists
