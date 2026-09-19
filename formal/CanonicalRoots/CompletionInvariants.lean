import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.AdicCompletion.Functoriality

noncomputable section
namespace CanonicalRoots

variable {R G M : Type*} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
  (I : Ideal R) (ρ : Representation R G M)

/-- Complete a representation using the existing functor on linear maps. -/
def adicRepresentation : Representation (AdicCompletion I R) G (AdicCompletion I M) where
  toFun g := AdicCompletion.map I (ρ g)
  map_one' := by
    rw [map_one]
    exact AdicCompletion.map_id I M
  map_mul' g h := by
    change AdicCompletion.map I (ρ (g * h)) =
      (AdicCompletion.map I (ρ g)).comp (AdicCompletion.map I (ρ h))
    rw [AdicCompletion.map_comp, map_mul]
    rfl

variable [Fintype G] [Invertible (Fintype.card G : R)]

/-- Reynolds projection with its actual invariant codomain. -/
def invariantProjection : M →ₗ[R] ρ.invariants :=
  ρ.averageMap.codRestrict _ ρ.averageMap_invariant

theorem invariantProjection_comp_subtype :
    (invariantProjection ρ).comp ρ.invariants.subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ρ.averageMap_id x x.property

theorem subtype_comp_invariantProjection :
    ρ.invariants.subtype.comp (invariantProjection ρ) = ρ.averageMap := rfl

/-- The canonical inclusion of completed invariants is split injective. -/
theorem adic_invariants_injective :
    Function.Injective (AdicCompletion.map I ρ.invariants.subtype) := by
  have h : (AdicCompletion.map I (invariantProjection ρ)).comp
      (AdicCompletion.map I ρ.invariants.subtype) = LinearMap.id := by
    rw [AdicCompletion.map_comp, invariantProjection_comp_subtype, AdicCompletion.map_id]
  have hleft : Function.LeftInverse (AdicCompletion.map I (invariantProjection ρ))
      (AdicCompletion.map I ρ.invariants.subtype) := fun x => LinearMap.congr_fun h x
  exact hleft.injective

omit [Fintype G] [Invertible (Fintype.card G : R)] in
theorem adic_invariants_fixed (x : AdicCompletion I ρ.invariants) (g : G) :
    adicRepresentation I ρ g (AdicCompletion.map I ρ.invariants.subtype x) =
      AdicCompletion.map I ρ.invariants.subtype x := by
  change AdicCompletion.map I (ρ g) (AdicCompletion.map I ρ.invariants.subtype x) = _
  rw [AdicCompletion.map_comp_apply]
  have h : (ρ g).comp ρ.invariants.subtype = ρ.invariants.subtype := by
    apply LinearMap.ext
    intro y
    exact y.property g
  rw [h]

/-- Averaging a completed fixed vector leaves it unchanged. -/
theorem adic_averageMap_eq_self (x : AdicCompletion I M)
    (hx : x ∈ (adicRepresentation I ρ).invariants) :
    AdicCompletion.map I ρ.averageMap x = x := by
  have hav : ρ.averageMap = ⅟(Fintype.card G : R) • ∑ g : G, ρ g := by
    simp [Representation.averageMap, GroupAlgebra.average]
  rw [hav]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply]
  have hfix (g : G) : AdicCompletion.map I (ρ g) x = x := hx g
  simp only [hfix, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, invOf_mul_self, one_smul]

/-- Completion commutes with finite-group invariants when the group order is invertible.
This statement is about the actual completion functor, with no exactness assumption. -/
theorem adic_invariants_range :
    LinearMap.range (AdicCompletion.map I ρ.invariants.subtype) =
      (adicRepresentation I ρ).invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩ g
    exact adic_invariants_fixed I ρ x g
  · intro x hx
    refine ⟨AdicCompletion.map I (invariantProjection ρ) x, ?_⟩
    rw [AdicCompletion.map_comp_apply, subtype_comp_invariantProjection]
    exact adic_averageMap_eq_self I ρ x hx

/-- The invariant submodule of the completed representation is an actual completed module. -/
def adicInvariantsEquiv :
    AdicCompletion I ρ.invariants ≃ₗ[AdicCompletion I R] (adicRepresentation I ρ).invariants :=
  (LinearEquiv.ofInjective (AdicCompletion.map I ρ.invariants.subtype)
    (adic_invariants_injective I ρ)).trans
      (LinearEquiv.ofEq _ _ (adic_invariants_range I ρ))

end CanonicalRoots
