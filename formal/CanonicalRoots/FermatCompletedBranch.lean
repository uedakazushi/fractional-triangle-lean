import CanonicalRoots.HypersurfaceNonregular
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian

noncomputable section
namespace CanonicalRoots

variable {B : Type*} [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]

theorem augmentationCompleted_isLocalRing (ε : B →ₐ[ℂ] ℂ) :
    IsLocalRing (AdicCompletion (RingHom.ker ε.toRingHom) B) := by
  let J := RingHom.ker ε.toRingHom
  let S := AdicCompletion J B
  let I := J.map (algebraMap B S)
  let : I.IsMaximal := AdicCompletion.isMaximal_map_of_le J J le_rfl (Ideal.fg_of_isNoetherianRing J)
  let : IsAdicComplete I S := AdicCompletion.isAdicComplete_self J (Ideal.fg_of_isNoetherianRing J)
  exact isLocalRing_of_isAdicComplete_maximal I

theorem augmentationCompleted_maximalIdeal (ε : B →ₐ[ℂ] ℂ) :
    letI := augmentationCompleted_isLocalRing ε
    IsLocalRing.maximalIdeal (AdicCompletion (RingHom.ker ε.toRingHom) B) =
      (RingHom.ker ε.toRingHom).map (algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B)) := by
  let : IsLocalRing (AdicCompletion (RingHom.ker ε.toRingHom) B) := augmentationCompleted_isLocalRing ε
  exact (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ le_rfl
    (Ideal.fg_of_isNoetherianRing _))).symm

/-- A nonzero simple Fermat coordinate lifts in the actual completion of the remaining coordinates.
Existence is supplied by mathlib's Hensel theorem for complete rings. -/
theorem completed_power_branch_exists (ε : B →ₐ[ℂ] ℂ) (q : ℕ) (hq : 0 < q)
    (b : B) (r : ℂ) (hr : r ≠ 0) (hroot : r ^ q + ε b = 0) :
    ∃ u : AdicCompletion (RingHom.ker ε.toRingHom) B,
      u ^ q + algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) b = 0 ∧
      u - algebraMap ℂ (AdicCompletion (RingHom.ker ε.toRingHom) B) r ∈
        (RingHom.ker ε.toRingHom).map (algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B)) := by
  let J := RingHom.ker ε.toRingHom
  let S := AdicCompletion J B
  let I := J.map (algebraMap B S)
  let : IsAdicComplete I S := AdicCompletion.isAdicComplete_self J (Ideal.fg_of_isNoetherianRing J)
  let f : Polynomial S := Polynomial.X ^ q + Polynomial.C (algebraMap B S b)
  let a₀ : S := algebraMap ℂ S r
  have hf : f.Monic := Polynomial.monic_X_pow_add_C _ (ne_of_gt hq)
  have hbase : (algebraMap ℂ B r) ^ q + b ∈ J := by
    change ε ((algebraMap ℂ B r) ^ q + b) = 0
    simpa using hroot
  have hval : f.eval a₀ ∈ I := by
    have h := Ideal.mem_map_of_mem (algebraMap B S) hbase
    have hscalar : algebraMap B S (algebraMap ℂ B r) = a₀ :=
      (IsScalarTower.algebraMap_apply ℂ B S r).symm
    simpa only [f, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, map_add, map_pow, hscalar] using h
  have ha : IsUnit a₀ := (isUnit_iff_ne_zero.mpr hr).map (algebraMap ℂ S)
  have hqS : IsUnit (q : S) := by
    have h := (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt hq) : (q : ℂ) ≠ 0)).map
      (algebraMap ℂ S)
    simpa only [map_natCast] using h
  have hder : IsUnit (f.derivative.eval a₀) := by
    simpa only [f, Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      add_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using
      hqS.mul (ha.pow (q - 1))
  obtain ⟨u, hu, hur⟩ := HenselianRing.is_henselian (R := S) (I := I) f hf a₀ hval
    (hder.map (Ideal.Quotient.mk I))
  exact ⟨u, by simpa only [Polynomial.IsRoot, f, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] using hu, hur⟩

/-- The lifted nonzero Fermat branch is unique with its prescribed residue. -/
theorem completed_power_branch_unique (ε : B →ₐ[ℂ] ℂ) (q : ℕ) (hq : 0 < q)
    (b : B) (r : ℂ) (hr : r ≠ 0)
    (u v : AdicCompletion (RingHom.ker ε.toRingHom) B)
    (hu : u ^ q + algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) b = 0)
    (hv : v ^ q + algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) b = 0)
    (hur : u - algebraMap ℂ (AdicCompletion (RingHom.ker ε.toRingHom) B) r ∈
      (RingHom.ker ε.toRingHom).map (algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B)))
    (hvr : v - algebraMap ℂ (AdicCompletion (RingHom.ker ε.toRingHom) B) r ∈
      (RingHom.ker ε.toRingHom).map (algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B))) : u = v := by
  let S := AdicCompletion (RingHom.ker ε.toRingHom) B
  let : IsLocalRing S := augmentationCompleted_isLocalRing ε
  rw [← augmentationCompleted_maximalIdeal ε] at hur hvr
  let a₀ : S := algebraMap ℂ S r
  have ha : IsUnit a₀ := (isUnit_iff_ne_zero.mpr hr).map (algebraMap ℂ S)
  have hunit : IsUnit u := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hum
    have ham : a₀ ∈ IsLocalRing.maximalIdeal S := by
      have h := (IsLocalRing.maximalIdeal S).sub_mem hum hur
      simpa only [sub_sub_cancel] using h
    exact (IsLocalRing.notMem_maximalIdeal.mpr ha) ham
  have hsub : ¬ IsUnit (u - v) := by
    have h := (IsLocalRing.maximalIdeal S).sub_mem hur hvr
    have hm : u - v ∈ IsLocalRing.maximalIdeal S := by
      convert h using 1
      ring
    exact hm
  have hqS : IsUnit (q : S) := by
    have h := (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt hq) : (q : ℂ) ≠ 0)).map
      (algebraMap ℂ S)
    simpa only [map_natCast] using h
  let f : Polynomial S := Polynomial.X ^ q + Polynomial.C (algebraMap B S b)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f) ?_ ?_ hsub ?_
  · simpa only [f, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hu
  · simpa only [f, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hv
  · simpa only [f, Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      add_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using
      hqS.mul (hunit.pow (q - 1))

end CanonicalRoots
