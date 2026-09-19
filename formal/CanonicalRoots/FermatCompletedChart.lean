import CanonicalRoots.FermatFormalChartResidue
import CanonicalRoots.AdicCompleteLift

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)
  (hv : ∑ i, v i ^ p i = 0)

abbrev FermatPointCompletion := AdicCompletion (RingHom.ker (fermatPoint p v hv).toRingHom)
  (AmbientRing p)

def fermatTailInclusion : MvPolynomial (Fin n) ℂ →ₐ[ℂ] AmbientRing p :=
  aeval (fun i => ambientQuotient p (X i.succ))

@[simp] theorem fermatPoint_comp_tail :
    (fermatPoint p v hv).comp (fermatTailInclusion p) = fermatTailPoint v := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, fermatTailInclusion, aeval_X, fermatPoint_X, fermatTailPoint]

theorem fermatTailInclusion_map_pointIdeal :
    (RingHom.ker (fermatTailPoint v).toRingHom).map (fermatTailInclusion p).toRingHom ≤
      RingHom.ker (fermatPoint p v hv).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change fermatPoint p v hv (fermatTailInclusion p x) = 0
  exact (DFunLike.congr_fun (fermatPoint_comp_tail p v hv) x).trans hx

/-- The remaining coordinates give a map in the reverse direction between the actual completions. -/
def fermatTailCompletedInclusion : FermatTailCompletion v →ₐ[ℂ] FermatPointCompletion p v hv :=
  adicIdealMap _ _ (fermatTailInclusion p) (fermatTailInclusion_map_pointIdeal p v hv)

@[simp] theorem fermatTailCompletedInclusion_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    fermatTailCompletedInclusion p v hv
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) f) =
      algebraMap (AmbientRing p) (FermatPointCompletion p v hv) (fermatTailInclusion p f) :=
  adicIdealMap_algebraMap _ _ _ _ f

theorem fermatTailCompletedInclusion_map_pointIdeal :
    ((RingHom.ker (fermatTailPoint v).toRingHom).map
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v))).map
        (fermatTailCompletedInclusion p v hv).toRingHom ≤
      (RingHom.ker (fermatPoint p v hv).toRingHom).map
        (algebraMap (AmbientRing p) (FermatPointCompletion p v hv)) :=
  adicIdealMap_map_ideal _ _ _ _

variable (hp : 0 < p 0) (hv0 : v 0 ≠ 0)

/-- The actual formal chart, extended to the completed point ring. -/
def fermatCompletedChart : FermatPointCompletion p v hv →ₐ[ℂ] FermatTailCompletion v := by
  let : IsAdicComplete ((RingHom.ker (fermatTailPoint v).toRingHom).map
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v))) (FermatTailCompletion v) :=
    AdicCompletion.isAdicComplete_self _ (Ideal.fg_of_isNoetherianRing _)
  exact adicCompleteLift _ _ (fermatFormalChart p v hp hv hv0)
    (fermatFormalChart_map_pointIdeal v p hp hv hv0)

@[simp] theorem fermatCompletedChart_algebraMap (f : AmbientRing p) :
    fermatCompletedChart p v hv hp hv0
      (algebraMap (AmbientRing p) (FermatPointCompletion p v hv) f) =
      fermatFormalChart p v hp hv hv0 f := by
  let : IsAdicComplete ((RingHom.ker (fermatTailPoint v).toRingHom).map
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v))) (FermatTailCompletion v) :=
    AdicCompletion.isAdicComplete_self _ (Ideal.fg_of_isNoetherianRing _)
  exact adicCompleteLift_algebraMap _ _ _ _ f

theorem fermatCompletedChart_map_pointIdeal :
    ((RingHom.ker (fermatPoint p v hv).toRingHom).map
      (algebraMap (AmbientRing p) (FermatPointCompletion p v hv))).map
        (fermatCompletedChart p v hv hp hv0).toRingHom ≤
      (RingHom.ker (fermatTailPoint v).toRingHom).map
        (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v)) := by
  let : IsAdicComplete ((RingHom.ker (fermatTailPoint v).toRingHom).map
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v))) (FermatTailCompletion v) :=
    AdicCompletion.isAdicComplete_self _ (Ideal.fg_of_isNoetherianRing _)
  exact adicCompleteLift_map_ideal _ _ _ _

end CanonicalRoots
