import CanonicalRoots.AugmentationCotangentSpan
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
namespace CanonicalRoots
open DirectSum

variable {A : Type*} [CommRing A] [Algebra ℂ A]
  (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜] (ε : A →ₐ[ℂ] ℂ)

/-- The degree `m` part of a product of two augmentation elements uses only
strictly smaller positive degrees. -/
theorem graded_projection_mul_mem (S : Subalgebra ℂ A) (m : ℕ)
    (hzero : ∀ z : A, GradedAlgebra.proj 𝒜 0 z = algebraMap ℂ A (ε z))
    (hind : ∀ k < m, ∀ z ∈ 𝒜 k, z ∈ S)
    (u v : RingHom.ker ε.toRingHom) :
    GradedAlgebra.proj 𝒜 m ((u : A) * v) ∈ S := by
  classical
  have hu0 : (decompose 𝒜 (u : A) 0 : A) = 0 := by
    change GradedAlgebra.proj 𝒜 0 (u : A) = 0
    rw [hzero, show ε (u : A) = 0 from u.property, map_zero]
  have hv0 : (decompose 𝒜 (v : A) 0 : A) = 0 := by
    change GradedAlgebra.proj 𝒜 0 (v : A) = 0
    rw [hzero, show ε (v : A) = 0 from v.property, map_zero]
  rw [← sum_support_decompose 𝒜 (u : A)]
  rw [Finset.sum_mul, map_sum]
  apply S.sum_mem
  intro i hi
  change (decompose 𝒜 ((decompose 𝒜 (u : A) i : A) * (v : A)) m : A) ∈ S
  by_cases him : i ≤ m
  · rw [coe_decompose_mul_of_left_mem_of_le 𝒜 (decompose 𝒜 (u : A) i).property him]
    by_cases hi0 : i = 0
    · subst i
      rw [hu0, zero_mul]
      exact S.zero_mem
    by_cases hie : i = m
    · subst i
      rw [Nat.sub_self, hv0, mul_zero]
      exact S.zero_mem
    exact S.mul_mem (hind i (by omega) _ (decompose 𝒜 (u : A) i).property)
      (hind (m - i) (by omega) _ (decompose 𝒜 (v : A) (m - i)).property)
  · rw [coe_decompose_mul_of_left_mem_of_not_le 𝒜 (decompose 𝒜 (u : A) i).property him]
    exact S.zero_mem

/-- Graded Nakayama in the form needed here: homogeneous representatives of a
spanning set of the origin cotangent space generate the connected graded algebra. -/
theorem graded_adjoin_eq_top_of_cotangent_span {ι : Type*} [Fintype ι]
    (hzero : ∀ z : A, GradedAlgebra.proj 𝒜 0 z = algebraMap ℂ A (ε z))
    (x : ι → RingHom.ker ε.toRingHom)
    (hx : ∀ i, ∃ d, (x i : A) ∈ 𝒜 d)
    (hspan : Submodule.span ℂ (Set.range (fun i =>
      (RingHom.ker ε.toRingHom).toCotangent (x i))) = ⊤) :
    Algebra.adjoin ℂ (Set.range (fun i => (x i : A))) = ⊤ := by
  classical
  let I := RingHom.ker ε.toRingHom
  let S := Algebra.adjoin ℂ (Set.range (fun i => (x i : A)))
  have hhom : ∀ m, ∀ z ∈ 𝒜 m, z ∈ S := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m hind =>
      intro z hz
      have hpz : GradedAlgebra.proj 𝒜 m z = z := decompose_of_mem_same 𝒜 hz
      by_cases hm : m = 0
      · subst m
        rw [← hpz, hzero]
        exact S.algebraMap_mem _
      have hzε : ε z = 0 := by
        have he := hzero z
        rw [GradedAlgebra.proj_apply, decompose_of_mem_ne 𝒜 hz hm] at he
        have := congrArg ε he
        simpa only [map_zero, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using this.symm
      let zI : I := ⟨z, hzε⟩
      have hzspan : I.toCotangent zI ∈ Submodule.span ℂ
          (Set.range (fun i => I.toCotangent (x i))) := by rw [hspan]; trivial
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzspan
      let l : I := ∑ i, c i • x i
      have hsquare : ((zI - l : I) : A) ∈ I ^ 2 := by
        apply (I.toCotangent_eq_zero _).mp
        change (I.toCotangent.restrictScalars ℂ) (zI - l) = 0
        simp only [map_sub, l, map_sum, map_smul, LinearMap.restrictScalars_apply]
        rw [hc, sub_self]
      have hproj_square : ∀ w ∈ I ^ 2, GradedAlgebra.proj 𝒜 m w ∈ S := by
        intro w hw
        rw [pow_two] at hw
        refine Submodule.mul_induction_on hw ?_ ?_
        · intro u hu v hv
          exact graded_projection_mul_mem 𝒜 ε S m hzero hind ⟨u, hu⟩ ⟨v, hv⟩
        · intro u v hu hv
          rw [map_add]
          exact S.add_mem hu hv
      have hlin : GradedAlgebra.proj 𝒜 m (l : A) ∈ S := by
        simp only [l, Submodule.coe_sum]
        rw [map_sum]
        apply S.sum_mem
        intro i hi
        change GradedAlgebra.proj 𝒜 m (c i • (x i : A)) ∈ S
        rw [map_smul]
        apply S.smul_mem
        obtain ⟨d, hd⟩ := hx i
        by_cases hdm : d = m
        · subst d
          rw [GradedAlgebra.proj_apply, decompose_of_mem_same 𝒜 hd]
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        · rw [GradedAlgebra.proj_apply, decompose_of_mem_ne 𝒜 hd hdm]
          exact S.zero_mem
      have hres := S.add_mem (hproj_square _ hsquare) hlin
      simpa only [Submodule.coe_sub, zI, map_sub, sub_add_cancel, hpz] using hres
  apply top_unique
  intro z hz
  change z ∈ S
  rw [← sum_support_decompose 𝒜 z]
  exact S.sum_mem fun m hm => hhom m _ (decompose 𝒜 z m).property

end CanonicalRoots
