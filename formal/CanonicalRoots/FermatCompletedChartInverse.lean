import CanonicalRoots.FermatCompletedChart

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)
  (hv : ∑ i, v i ^ p i = 0) (hp : 0 < p 0) (hv0 : v 0 ≠ 0)

theorem fermatTailInclusion_relation :
    ambientQuotient p (X 0) ^ p 0 + fermatTailInclusion p (fermat (fun i => p i.succ)) = 0 := by
  have h : ambientQuotient p (fermat p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [fermat, map_add, map_sum, map_pow, Fin.sum_univ_succ, fermatTailInclusion, aeval_X] using h

/-- Uniqueness of the Hensel branch identifies the recovered coordinate with the original one. -/
theorem fermatTailCompletedInclusion_branch :
    fermatTailCompletedInclusion p v hv (fermatCompletedBranch p v hp hv hv0) =
      algebraMap (AmbientRing p) (FermatPointCompletion p v hv) (ambientQuotient p (X 0)) := by
  apply completed_power_branch_unique (fermatPoint p v hv) (p 0) hp
    (fermatTailInclusion p (fermat (fun i => p i.succ))) (v 0) hv0
  · have h := congrArg (fermatTailCompletedInclusion p v hv) (fermatCompletedBranch_equation p v hp hv hv0)
    simpa only [map_add, map_pow, map_zero, fermatTailCompletedInclusion_algebraMap] using h
  · have h := congrArg (algebraMap (AmbientRing p) (FermatPointCompletion p v hv))
      (fermatTailInclusion_relation p)
    simpa only [map_add, map_pow, map_zero] using h
  · have h := Ideal.mem_map_of_mem (fermatTailCompletedInclusion p v hv).toRingHom
      (fermatCompletedBranch_residue p v hp hv hv0)
    have hm := fermatTailCompletedInclusion_map_pointIdeal p v hv h
    change fermatTailCompletedInclusion p v hv
      (fermatCompletedBranch p v hp hv hv0 - algebraMap ℂ (FermatTailCompletion v) (v 0)) ∈ _ at hm
    simpa only [map_sub, AlgHom.commutes] using hm
  · have h : ambientQuotient p (X 0) - algebraMap ℂ (AmbientRing p) (v 0) ∈
        RingHom.ker (fermatPoint p v hv).toRingHom := by
      change fermatPoint p v hv (ambientQuotient p (X 0) - algebraMap ℂ (AmbientRing p) (v 0)) = 0
      simp only [map_sub, fermatPoint_X, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have hm := Ideal.mem_map_of_mem (algebraMap (AmbientRing p) (FermatPointCompletion p v hv)) h
    simpa only [map_sub, ← IsScalarTower.algebraMap_apply] using hm

/-- On the original Fermat quotient, inclusion after the chart is the canonical completion map. -/
theorem fermatTailCompletedInclusion_chart (x : AmbientRing p) :
    fermatTailCompletedInclusion p v hv (fermatFormalChart p v hp hv hv0 x) =
      algebraMap (AmbientRing p) (FermatPointCompletion p v hv) x := by
  have he : ((fermatTailCompletedInclusion p v hv).comp (fermatFormalChart p v hp hv hv0)).comp
      (ambientQuotient p) = ((IsScalarTower.toAlgHom ℂ (AmbientRing p)
        (FermatPointCompletion p v hv)).comp (ambientQuotient p)) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, fermatFormalChart_X_zero, fermatTailCompletedInclusion_branch]
      rfl
    | succ i =>
      simp only [AlgHom.comp_apply, fermatFormalChart_X_succ,
        fermatTailCompletedInclusion_algebraMap, fermatTailInclusion, aeval_X]
      rfl
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (fermatIdeal p) x
  exact DFunLike.congr_fun he f

/-- On the original tail polynomial ring, the chart after inclusion is the completion map. -/
theorem fermatCompletedChart_tail_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    fermatCompletedChart p v hv hp hv0 (fermatTailCompletedInclusion p v hv
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) f)) =
        algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) f := by
  rw [fermatTailCompletedInclusion_algebraMap, fermatCompletedChart_algebraMap]
  have he : (fermatFormalChart p v hp hv hv0).comp (fermatTailInclusion p) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, fermatTailInclusion, aeval_X, fermatFormalChart_X_succ]
    rfl
  exact DFunLike.congr_fun he f

end CanonicalRoots
