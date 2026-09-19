import CanonicalRoots

noncomputable section
namespace CanonicalRoots.CotangentTests
open MvPolynomial IsLocalRing

def node : MvPolynomial (Fin 3) ℂ := cyclicQuotientEquation 0 1 2 2
def transverseFive : MvPolynomial (Fin 5) ℂ := cyclicQuotientEquation 0 1 2 7

theorem node_minimal : HasNoConstantOrLinear node :=
  cyclicQuotientEquation_noConstantOrLinear 0 1 2 2 (by decide)

theorem node_cotangent_dimension :
    Module.finrank (ResidueField (PresentedOriginLocalRing node node_minimal.1))
      (CotangentSpace (PresentedOriginLocalRing node node_minimal.1)) = 3 :=
  presentedLocalCotangent_finrank node node_minimal

theorem node_nonregular : ¬ IsRegularLocalRing (PresentedOriginLocalRing node node_minimal.1) :=
  cyclicQuotient_origin_not_regular 0 1 2 2 (by decide) (by decide) (by decide)

theorem node_not_two_generated
    (q : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] PresentedRing node) : ¬ Function.Surjective q := by
  intro hq
  have := presented_minimum_generators node node_minimal q hq
  omega

theorem transverseFive_minimal : HasNoConstantOrLinear transverseFive :=
  cyclicQuotientEquation_noConstantOrLinear 0 1 2 7 (by decide)

theorem transverseFive_cotangent_dimension :
    Module.finrank (ResidueField (PresentedOriginLocalRing transverseFive transverseFive_minimal.1))
      (CotangentSpace (PresentedOriginLocalRing transverseFive transverseFive_minimal.1)) = 5 :=
  presentedLocalCotangent_finrank transverseFive transverseFive_minimal

theorem transverseFive_nonregular :
    ¬ IsRegularLocalRing (PresentedOriginLocalRing transverseFive transverseFive_minimal.1) :=
  cyclicQuotient_origin_not_regular 0 1 2 7 (by decide) (by decide) (by decide)

/-- The linear boundary is deliberately excluded by the minimality hypothesis. -/
theorem linear_relation_excluded : ¬ HasNoConstantOrLinear (X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) := by
  intro h
  have := h.2 0
  simp at this

end CanonicalRoots.CotangentTests
