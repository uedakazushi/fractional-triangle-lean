import CanonicalRoots.CyclicPlaneInvariants
import CanonicalRoots.AugmentationLocalEquiv

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def cyclicPlaneOrigin (s : ℕ) : cyclicPlaneFixed s →ₐ[ℂ] ℂ :=
  (aeval (fun _ : Fin 2 => (0 : ℂ))).comp (cyclicPlaneFixed s).val

@[simp] theorem cyclicQuotientEquivFixed_coe (s : ℕ) (hs : 0 < s) (x : CyclicModelRing s) :
    (cyclicQuotientEquivFixed s hs x : MvPolynomial (Fin 2) ℂ) = cyclicQuotientMap s x := rfl

theorem cyclicQuotientEquivFixed_origin (s : ℕ) (hs : 2 ≤ s) :
    (cyclicPlaneOrigin s).comp (cyclicQuotientEquivFixed s (by omega)).toAlgHom =
      presentedAugmentation (cyclicQuotientEquation (1 : Fin 3) 2 0 s)
        (cyclicQuotientEquation_noConstantOrLinear 1 2 0 s hs).1 := by
  have he : (aeval (fun _ : Fin 2 => (0 : ℂ))).comp (cyclicPolynomialMap s) =
      aeval (fun _ : Fin 3 => (0 : ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cyclicPolynomialMap, show s ≠ 0 by omega]
  apply AlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ
    (Ideal.span {cyclicQuotientEquation (1 : Fin 3) 2 0 s}) x
  change aeval (fun _ : Fin 2 => (0 : ℂ))
    (cyclicQuotientEquivFixed s (by omega) (Ideal.Quotient.mkₐ ℂ _ f) : MvPolynomial (Fin 2) ℂ) =
      aeval (fun _ : Fin 3 => (0 : ℂ)) f
  rw [cyclicQuotientEquivFixed_coe, cyclicQuotientMap_mk]
  exact DFunLike.congr_fun he f

/-- The actual cyclic fixed algebra has the stated local hypersurface model at the origin. -/
def cyclicInvariantOriginEquiv (s : ℕ) (hs : 2 ≤ s) :
    PresentedOriginLocalRing (cyclicQuotientEquation (1 : Fin 3) 2 0 s)
      (cyclicQuotientEquation_noConstantOrLinear 1 2 0 s hs).1 ≃ₐ[ℂ]
        AugmentationLocalRing (cyclicPlaneOrigin s) :=
  augmentationLocalEquiv _ _ (cyclicQuotientEquivFixed s (by omega))
    (cyclicQuotientEquivFixed_origin s hs)

theorem cyclicPlaneFixed_origin_not_regular (s : ℕ) (hs : 2 ≤ s) :
    ¬ IsRegularLocalRing (AugmentationLocalRing (cyclicPlaneOrigin s)) := by
  intro h
  let : IsRegularLocalRing (AugmentationLocalRing (cyclicPlaneOrigin s)) := h
  exact cyclicQuotient_origin_not_regular (1 : Fin 3) 2 0 s hs (by decide) (by decide)
    (IsRegularLocalRing.of_ringEquiv (cyclicInvariantOriginEquiv s hs).symm.toRingEquiv)

end CanonicalRoots
