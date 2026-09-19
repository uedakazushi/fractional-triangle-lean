import CanonicalRoots.FiniteInvariantFibers
import CanonicalRoots.AdicCofinality
import CanonicalRoots.AdicChineseRemainder
import CanonicalRoots.LocalCompletion
import CanonicalRoots.RootCompletedAlgebra

noncomputable section
namespace CanonicalRoots

def adicIdealCongr {R : Type*} [CommRing R] (I J : Ideal R) (h : I = J) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion J R := by
  subst J
  exact AlgEquiv.refl

section General
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [IsNoetherianRing S] (J : Ideal R) [J.IsMaximal]

/-- The completion of a finite extension along a closed fiber splits over its actual primes. -/
def finiteFiberCompletionEquiv :
    AdicCompletion (J.map (algebraMap R S)) S ≃ₐ[S]
      (∀ Q : J.primesOver S, AdicCompletion Q.val S) := by
  let : Fintype (J.primesOver S) := (Algebra.QuasiFinite.finite_primesOver J).fintype
  have hcop : Pairwise (fun Q P : J.primesOver S => IsCoprime Q.val P.val) := by
    intro Q P hQP
    exact Ideal.isCoprime_of_isMaximal (fun he => hQP (Subtype.ext he))
  exact ((adicRadicalEquiv (J.map (algebraMap R S)) (Ideal.fg_of_isNoetherianRing _)).trans
    (adicIdealCongr _ _ (radical_map_eq_iInf_primesOver J))).trans
      (adicChineseRemainderEquiv (fun Q : J.primesOver S => Q.val) hcop)

/-- Each factor is the completion of the actual point localization, not a replacement ring. -/
def finiteFiberLocalCompletionEquiv :
    AdicCompletion (J.map (algebraMap R S)) S ≃ₐ[S]
      (∀ Q : J.primesOver S,
        AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q.val))
          (Localization.AtPrime Q.val)) :=
  (finiteFiberCompletionEquiv J).trans
    (AlgEquiv.piCongrRight (fun Q : J.primesOver S => localCompletionEquiv Q.val (Localization.AtPrime Q.val)))

end General

set_option backward.isDefEq.respectTransparency.types false in
/-- The complete finite Fermat extension splits into its actual completed local rings. -/
def rootFiberLocalCompletionEquiv {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (J : Ideal (RootRing p τ)) [J.IsMaximal] :
    AmbientRootCompletion p τ J ≃ₐ[AmbientRing p]
      (∀ Q : J.primesOver (AmbientRing p),
        AdicCompletion (R := Localization.AtPrime Q.val)
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q.val))
          (Localization.AtPrime Q.val)) := by
  let : Module.Finite (RootRing p τ) (AmbientRing p) := ambient_finite_over_root p hp ha τ hτ
  exact finiteFiberLocalCompletionEquiv J

end CanonicalRoots
