import CanonicalRoots.FiniteFiberCompletion
import CanonicalRoots.AdicIdealFunctor

noncomputable section
namespace CanonicalRoots

variable {S ι : Type*} [CommRing S]

/-- The forward cofinal Chinese-remainder map has the canonical quotient projections. -/
theorem cofinalChinese_apply [Fintype ι] (L : ι → Ideal S)
    (hL : Pairwise (fun i j => IsCoprime (L i) (L j)))
    (I K : Ideal S) (hIK : I ≤ K) (k : ℕ) (hk : 1 ≤ k) (hKI : K ^ k ≤ I)
    (hK : K = ⨅ i, L i) (i : ι) (hi : I ≤ L i) (x : AdicCompletion I S) :
    (((adicCofinalEquiv I K hIK k hk hKI).trans (adicIdealCongr K _ hK)).trans
      (adicChineseRemainderEquiv L hL) x) i =
        adicRefinement I (L i) id monotone_id (fun n => pow_le_pow_left' hi n) x := by
  subst K
  apply Subtype.ext
  funext n
  change adicChineseQuotientEquiv L hL n
      (adicRefinementQuotient I (⨅ i, L i) id _ n (x.val n)) i =
    adicRefinementQuotient I (L i) id _ n (x.val n)
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

variable {R : Type*} [CommRing R] [Algebra R S]

/-- Canonical projection from the completion along a closed fiber to one point completion. -/
def finiteFiberProjection (J : Ideal R) [J.IsMaximal] (Q : J.primesOver S) :
    AdicCompletion (J.map (algebraMap R S)) S →ₐ[S] AdicCompletion Q.val S :=
  adicRefinement _ _ id monotone_id (fun n => pow_le_pow_left'
    ((liesOver_maximal_iff_map_le J Q.val).mp Q.property.2) n)

theorem finiteFiberCompletionEquiv_apply [Module.Finite R S] [IsNoetherianRing S]
    (J : Ideal R) [J.IsMaximal] (Q : J.primesOver S)
    (x : AdicCompletion (J.map (algebraMap R S)) S) :
    finiteFiberCompletionEquiv J x Q = finiteFiberProjection J Q x := by
  let : Fintype (J.primesOver S) := (Algebra.QuasiFinite.finite_primesOver J).fintype
  unfold finiteFiberCompletionEquiv adicRadicalEquiv finiteFiberProjection
  exact cofinalChinese_apply _ _ _ _ _ _ _ _ _ Q
    ((liesOver_maximal_iff_map_le J Q.val).mp Q.property.2) x

end CanonicalRoots
