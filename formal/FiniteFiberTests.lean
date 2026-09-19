import CanonicalRoots.FiniteFiberCompletion

noncomputable section
namespace CanonicalRoots.FiniteFiberTests

/-- The decomposition requires neither a domain nor a reduced ambient ring. -/
example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [IsNoetherianRing S] (J : Ideal R) [J.IsMaximal] :
    Nonempty (AdicCompletion (J.map (algebraMap R S)) S ≃ₐ[S]
      (∀ Q : J.primesOver S, AdicCompletion Q.val S)) :=
  ⟨finiteFiberCompletionEquiv J⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness and the local factors are proved for the original Fermat/root rings. -/
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (J : Ideal (RootRing p τ)) [J.IsMaximal] :
    Nonempty (AmbientRootCompletion p τ J ≃ₐ[AmbientRing p]
      (∀ Q : J.primesOver (AmbientRing p),
        AdicCompletion (R := Localization.AtPrime Q.val)
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q.val))
          (Localization.AtPrime Q.val))) :=
  ⟨rootFiberLocalCompletionEquiv p hp ha τ hτ J⟩

/-- The cofinality construction applies to a nontrivial change of powers. -/
example {R : Type*} [CommRing R] (I : Ideal R) :
    Nonempty (AdicCompletion (I ^ 2) R ≃ₐ[R] AdicCompletion I R) := by
  exact ⟨adicCofinalEquiv (I ^ 2) I (Ideal.pow_le_self (by decide)) 2 (by decide) le_rfl⟩

end CanonicalRoots.FiniteFiberTests
