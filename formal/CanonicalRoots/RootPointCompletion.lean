import CanonicalRoots.RootFiberInvariants
import CanonicalRoots.SupportedInvariantLift

noncomputable section
namespace CanonicalRoots

/-- For a rational point, preserving its kernel is precisely preserving its value map. -/
theorem augmentation_map_kernel_iff {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    (z : S →ₐ[k] k) (e : S ≃ₐ[k] S) :
    (RingHom.ker z.toRingHom).map e = RingHom.ker z.toRingHom ↔ z.comp e.toAlgHom = z := by
  constructor
  · intro h
    apply AlgHom.ext
    intro x
    have hx : x - algebraMap k S (z x) ∈ RingHom.ker z.toRingHom := by
      change z (x - algebraMap k S (z x)) = 0
      rw [map_sub, z.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have he := Ideal.mem_map_of_mem e hx
    rw [h] at he
    change z (e (x - algebraMap k S (z x))) = 0 at he
    change z (e x) = z x
    simpa only [map_sub, AlgEquiv.commutes, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_eq_zero] using he
  · intro h
    have he (x : S) : z (e x) = z x := DFunLike.congr_fun h x
    apply Ideal.ext
    intro x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (he y).trans hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change z (e.symm x) = 0
      rw [← he, e.apply_symm_apply]
      exact hx

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (z : AmbientRing p →ₐ[ℂ] ℂ)

/-- The original ambient point, regarded as a prime over its image in the root ring. -/
def rootFiberPoint : (RingHom.ker (rootPoint p τ z).toRingHom).primesOver (AmbientRing p) :=
  ⟨RingHom.ker z.toRingHom, inferInstance, ⟨rfl⟩⟩

theorem rootFiberPoint_stabilizer_iff (χ : RootCharacter p τ) :
    fiberPrimeEquiv (RingHom.ker (rootPoint p τ z).toRingHom)
      (ambientRootAlgEquiv p τ χ) (rootFiberPoint p τ z) = rootFiberPoint p τ z ↔
        χ ∈ rootPointStabilizer p τ z := by
  rw [Subtype.ext_iff]
  exact augmentation_map_kernel_iff z (ambientCharacterEquiv p τ χ)

theorem rootPointStabilizer_map_kernel (χ : rootPointStabilizer p τ z) :
    (RingHom.ker z.toRingHom).map (ambientRootAlgHom p τ χ.val).toRingHom =
      RingHom.ker z.toRingHom :=
  (augmentation_map_kernel_iff z (ambientCharacterEquiv p τ χ.val)).mpr χ.property

/-- The stabilizer acts on the completion at the actual ambient point ideal. -/
def pointCompletedCharacterHom (χ : rootPointStabilizer p τ z) :
    AdicCompletion (RingHom.ker z.toRingHom) (AmbientRing p) →ₐ[RootRing p τ]
      AdicCompletion (RingHom.ker z.toRingHom) (AmbientRing p) :=
  adicIdealMap _ _ (ambientRootAlgHom p τ χ.val) (rootPointStabilizer_map_kernel p τ z χ).le

def rootPointCompletedProjection :
    AmbientRootCompletion p τ (RingHom.ker (rootPoint p τ z).toRingHom) →ₐ[RootRing p τ]
      AdicCompletion (RingHom.ker z.toRingHom) (AmbientRing p) :=
  (finiteFiberProjection _ (rootFiberPoint p τ z)).restrictScalars (RootRing p τ)

theorem rootPointCompletedProjection_equivariant (χ : rootPointStabilizer p τ z)
    (x : AmbientRootCompletion p τ (RingHom.ker (rootPoint p τ z).toRingHom)) :
    rootPointCompletedProjection p τ z
      (completedRootCharacterHom p τ (RingHom.ker (rootPoint p τ z).toRingHom) χ.val x) =
    pointCompletedCharacterHom p τ z χ (rootPointCompletedProjection p τ z x) := by
  exact finiteFiberProjection_equivariant_fixed _ (ambientRootAlgHom p τ χ.val)
    (rootFiberPoint p τ z) (rootPointStabilizer_map_kernel p τ z χ).le x

/-- The stabilizer fixed algebra inside the actual point-ideal completion. -/
def pointCompletedFixed :
    Subalgebra (RootRing p τ) (AdicCompletion (RingHom.ker z.toRingHom) (AmbientRing p)) where
  carrier := {x | ∀ χ : rootPointStabilizer p τ z, pointCompletedCharacterHom p τ z χ x = x}
  zero_mem' χ := map_zero _
  one_mem' χ := map_one _
  add_mem' hx hy χ := by rw [map_add, hx χ, hy χ]
  mul_mem' hx hy χ := by rw [map_mul, hx χ, hy χ]
  algebraMap_mem' r χ := (pointCompletedCharacterHom p τ z χ).commutes r

def rootCompletedFixedToPoint :
    completedRootFixed p τ (RingHom.ker (rootPoint p τ z).toRingHom) →ₐ[RootRing p τ]
      pointCompletedFixed p τ z :=
  ((rootPointCompletedProjection p τ z).comp
    (completedRootFixed p τ (RingHom.ker (rootPoint p τ z).toRingHom)).val).codRestrict
      (pointCompletedFixed p τ z) (fun x χ => by
        change pointCompletedCharacterHom p τ z χ (rootPointCompletedProjection p τ z x.val) =
          rootPointCompletedProjection p τ z x.val
        rw [← rootPointCompletedProjection_equivariant, x.property χ.val])

end CanonicalRoots
