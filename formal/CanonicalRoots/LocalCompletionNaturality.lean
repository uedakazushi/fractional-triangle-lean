import CanonicalRoots.LocalCompletion
import CanonicalRoots.AdicIdealFunctor

noncomputable section
namespace CanonicalRoots

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S]
  (J : Ideal R) [J.IsMaximal] [IsLocalization.AtPrime S J] [IsLocalRing S]

/-- The actual localization-completion equivalence respects compatible ideal-preserving maps. -/
theorem localCompletionEquiv_natural (f : R →ₐ[k] R) (g : S →ₐ[k] S)
    (hf : J.map f.toRingHom ≤ J)
    (hg : (IsLocalRing.maximalIdeal S).map g.toRingHom ≤ IsLocalRing.maximalIdeal S)
    (hfg : ∀ r : R, g (algebraMap R S r) = algebraMap R S (f r)) (x : AdicCompletion J R) :
    localCompletionEquiv J S (adicIdealMap J J f hf x) =
      adicIdealMap _ _ g hg (localCompletionEquiv J S x) := by
  apply Subtype.ext
  funext n
  change localAdicQuotientEquiv J S n (adicIdealQuotientMap J J f hf n (x.val n)) =
    adicIdealQuotientMap _ _ g hg n (localAdicQuotientEquiv J S n (x.val n))
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with
  | _ y => exact congrArg (Ideal.Quotient.mk _) (hfg y).symm

end CanonicalRoots
