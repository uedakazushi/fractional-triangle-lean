import CanonicalRoots.AdicIdealFunctor
import Mathlib.RingTheory.AdicCompletion.LocalRing

noncomputable section
namespace CanonicalRoots

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

@[simp] theorem adicIdealMap_algebraMap (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)
    (h : I.map f.toRingHom ≤ J) (x : R) :
    adicIdealMap I J f h (algebraMap R (AdicCompletion I R) x) =
      algebraMap S (AdicCompletion J S) (f x) := by
  apply Subtype.ext
  funext n
  rfl

theorem adicIdealMap_map_ideal (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)
    (h : I.map f.toRingHom ≤ J) :
    (I.map (algebraMap R (AdicCompletion I R))).map (adicIdealMap I J f h).toRingHom ≤
      J.map (algebraMap S (AdicCompletion J S)) := by
  rw [Ideal.map_map]
  have he : (adicIdealMap I J f h).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f.toRingHom := by
    apply RingHom.ext
    intro x
    exact adicIdealMap_algebraMap I J f h x
  rw [he, ← Ideal.map_map]
  exact Ideal.map_mono h

/-- Extend an ideal-preserving map to a complete target. -/
def adicCompleteLift (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
    (f : R →ₐ[k] S) (h : I.map f.toRingHom ≤ J) : AdicCompletion I R →ₐ[k] S :=
  ((AdicCompletion.ofAlgEquiv J).symm.toAlgHom.restrictScalars k).comp
    (adicIdealMap I J f h)

@[simp] theorem adicCompleteLift_algebraMap (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
    (f : R →ₐ[k] S) (h : I.map f.toRingHom ≤ J) (x : R) :
    adicCompleteLift I J f h (algebraMap R (AdicCompletion I R) x) = f x := by
  change (AdicCompletion.ofAlgEquiv J).symm
    (adicIdealMap I J f h (algebraMap R (AdicCompletion I R) x)) = f x
  rw [adicIdealMap_algebraMap]
  exact AdicCompletion.ofAlgEquiv_symm_of J (f x)

/-- The extension preserves the extended ideal. -/
theorem adicCompleteLift_map_ideal (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
    (f : R →ₐ[k] S) (h : I.map f.toRingHom ≤ J) :
    (I.map (algebraMap R (AdicCompletion I R))).map (adicCompleteLift I J f h).toRingHom ≤ J := by
  rw [Ideal.map_map]
  have he : (adicCompleteLift I J f h).toRingHom.comp
      (algebraMap R (AdicCompletion I R)) = f.toRingHom := by
    apply RingHom.ext
    intro x
    exact adicCompleteLift_algebraMap I J f h x
  rw [he]
  exact h

/-- Every element of a finitely generated ideal's completion has an original-ring
approximation modulo each power of the extended ideal. -/
theorem adicCompletion_approx (I : Ideal R) (hI : I.FG) (x : AdicCompletion I R) (n : ℕ) :
    ∃ r : R, x - algebraMap R (AdicCompletion I R) r ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  obtain ⟨r, hr⟩ := (Submodule.mkQ_surjective (I ^ n • ⊤ : Ideal R)) (x.val n)
  refine ⟨r, ?_⟩
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := R) hI]
  change AdicCompletion.eval I R n (x - AdicCompletion.of I R r) = 0
  rw [map_sub, AdicCompletion.eval_of]
  exact sub_eq_zero.mpr hr.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Ideal-preserving maps out of a completion are determined by their values on the
original ring. The ideal bounds supply the required continuity. -/
theorem adicCompletion_algHom_ext (I : Ideal R) (hI : I.FG) (J : Ideal S) [IsHausdorff J S]
    (f g : AdicCompletion I R →ₐ[k] S)
    (hf : (I.map (algebraMap R (AdicCompletion I R))).map f.toRingHom ≤ J)
    (hg : (I.map (algebraMap R (AdicCompletion I R))).map g.toRingHom ≤ J)
    (hfg : ∀ r : R, f (algebraMap R (AdicCompletion I R) r) =
      g (algebraMap R (AdicCompletion I R) r)) : f = g := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n x
  obtain ⟨r, hr⟩ := adicCompletion_approx I hI x n
  have hf' : f x - f (algebraMap R (AdicCompletion I R) r) ∈ J ^ n := by
    have h := Ideal.mem_map_of_mem f.toRingHom hr
    rw [Ideal.map_pow] at h
    change f (x - algebraMap R (AdicCompletion I R) r) ∈ _ at h
    rw [map_sub] at h
    exact (pow_le_pow_left' hf n) h
  have hg' : g x - g (algebraMap R (AdicCompletion I R) r) ∈ J ^ n := by
    have h := Ideal.mem_map_of_mem g.toRingHom hr
    rw [Ideal.map_pow] at h
    change g (x - algebraMap R (AdicCompletion I R) r) ∈ _ at h
    rw [map_sub] at h
    exact (pow_le_pow_left' hg n) h
  exact (Ideal.Quotient.eq.mpr hf').trans
    ((congrArg (Ideal.Quotient.mk (J ^ n)) (hfg r)).trans (Ideal.Quotient.eq.mpr hg').symm)

end CanonicalRoots
