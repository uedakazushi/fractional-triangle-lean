import CanonicalRoots.FermatCompletedChartInverse
import CanonicalRoots.LocalCompletion

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)
  (hv : ∑ i, v i ^ p i = 0) (hp : 0 < p 0) (hv0 : v 0 ≠ 0)

theorem fermatCompletedChart_comp_tail :
    (fermatCompletedChart p v hv hp hv0).comp (fermatTailCompletedInclusion p v hv) =
      AlgHom.id ℂ (FermatTailCompletion v) := by
  let I := RingHom.ker (fermatTailPoint v).toRingHom
  let J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v))
  let : IsAdicComplete J (FermatTailCompletion v) :=
    AdicCompletion.isAdicComplete_self I (Ideal.fg_of_isNoetherianRing I)
  apply adicCompletion_algHom_ext I (Ideal.fg_of_isNoetherianRing I) J
  · change J.map ((fermatCompletedChart p v hv hp hv0).toRingHom.comp
        (fermatTailCompletedInclusion p v hv).toRingHom) ≤ J
    rw [← Ideal.map_map]
    exact (Ideal.map_mono (fermatTailCompletedInclusion_map_pointIdeal p v hv)).trans
      (fermatCompletedChart_map_pointIdeal p v hv hp hv0)
  · exact le_of_eq (Ideal.map_id J)
  · intro f
    exact fermatCompletedChart_tail_algebraMap p v hv hp hv0 f

theorem fermatTailCompletedInclusion_comp_chart :
    (fermatTailCompletedInclusion p v hv).comp (fermatCompletedChart p v hv hp hv0) =
      AlgHom.id ℂ (FermatPointCompletion p v hv) := by
  let I := RingHom.ker (fermatPoint p v hv).toRingHom
  let J := I.map (algebraMap (AmbientRing p) (FermatPointCompletion p v hv))
  let : IsAdicComplete J (FermatPointCompletion p v hv) :=
    AdicCompletion.isAdicComplete_self I (Ideal.fg_of_isNoetherianRing I)
  apply adicCompletion_algHom_ext I (Ideal.fg_of_isNoetherianRing I) J
  · change J.map ((fermatTailCompletedInclusion p v hv).toRingHom.comp
        (fermatCompletedChart p v hv hp hv0).toRingHom) ≤ J
    rw [← Ideal.map_map]
    exact (Ideal.map_mono (fermatCompletedChart_map_pointIdeal p v hv hp hv0)).trans
      (fermatTailCompletedInclusion_map_pointIdeal p v hv)
  · exact le_of_eq (Ideal.map_id J)
  · intro f
    change fermatTailCompletedInclusion p v hv
      (fermatCompletedChart p v hv hp hv0 (algebraMap (AmbientRing p) (FermatPointCompletion p v hv) f)) = _
    rw [fermatCompletedChart_algebraMap]
    exact fermatTailCompletedInclusion_chart p v hv hp hv0 f

/-- At a point with nonzero zeroth coordinate, the completed Fermat ring is the
actual completed polynomial ring in the remaining coordinates. Both inverse identities
are proved, using Hensel uniqueness and ideal-adic separation. -/
def fermatCompletedChartEquiv : FermatPointCompletion p v hv ≃ₐ[ℂ] FermatTailCompletion v :=
  AlgEquiv.ofAlgHom (fermatCompletedChart p v hv hp hv0) (fermatTailCompletedInclusion p v hv)
    (fermatCompletedChart_comp_tail p v hv hp hv0)
    (fermatTailCompletedInclusion_comp_chart p v hv hp hv0)

@[simp] theorem fermatCompletedChartEquiv_algebraMap (x : AmbientRing p) :
    fermatCompletedChartEquiv p v hv hp hv0
      (algebraMap (AmbientRing p) (FermatPointCompletion p v hv) x) =
        fermatFormalChart p v hp hv hv0 x := fermatCompletedChart_algebraMap p v hv hp hv0 x

@[simp] theorem fermatCompletedChartEquiv_symm_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    (fermatCompletedChartEquiv p v hv hp hv0).symm
      (algebraMap (MvPolynomial (Fin n) ℂ) (FermatTailCompletion v) f) =
        algebraMap (AmbientRing p) (FermatPointCompletion p v hv) (fermatTailInclusion p f) :=
  fermatTailCompletedInclusion_algebraMap p v hv f

/-- The chart also identifies the completion of the actual localization at the Fermat point. -/
def fermatLocalCompletedChartEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing (fermatPoint p v hv)))
      (AugmentationLocalRing (fermatPoint p v hv)) ≃ₐ[ℂ] FermatTailCompletion v :=
  (augmentationCompletionEquiv (fermatPoint p v hv)).symm.trans
    (fermatCompletedChartEquiv p v hv hp hv0)

end CanonicalRoots
