import CanonicalRoots.FiniteFiberProjection

noncomputable section
namespace CanonicalRoots

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An automorphism over the base permutes the actual primes in each fiber. -/
def fiberPrimeEquiv (J : Ideal R) (e : S ≃ₐ[R] S) : J.primesOver S ≃ J.primesOver S where
  toFun Q := ⟨Q.val.map e, inferInstance, inferInstance⟩
  invFun Q := ⟨Q.val.map e.symm, inferInstance, inferInstance⟩
  left_inv Q := by
    apply Subtype.ext
    change (Q.val.map e.toRingHom).map e.symm.toRingHom = Q.val
    rw [Ideal.map_map]
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id S := by ext x; exact e.symm_apply_apply x
    rw [he, Ideal.map_id]
  right_inv Q := by
    apply Subtype.ext
    change (Q.val.map e.symm.toRingHom).map e.toRingHom = Q.val
    rw [Ideal.map_map]
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by ext x; exact e.apply_symm_apply x
    rw [he, Ideal.map_id]

/-- The transport between completed factors is induced by the original ring automorphism. -/
def fiberCompletionTransport (J : Ideal R) (e : S ≃ₐ[R] S) (Q : J.primesOver S) :
    AdicCompletion Q.val S ≃ₐ[R] AdicCompletion (fiberPrimeEquiv J e Q).val S :=
  adicIdealEquiv Q.val (fiberPrimeEquiv J e Q).val e rfl

/-- Equivariance of the canonical projections to point completions. -/
theorem finiteFiberProjection_equivariant (J : Ideal R) [J.IsMaximal]
    (e : S ≃ₐ[R] S) (Q : J.primesOver S)
    (x : AdicCompletion (J.map (algebraMap R S)) S) :
    finiteFiberProjection J (fiberPrimeEquiv J e Q) (adicAlgebraMap J e.toAlgHom x) =
      fiberCompletionTransport J e Q (finiteFiberProjection J Q x) := by
  apply Subtype.ext
  funext n
  change adicRefinementQuotient _ _ id _ n ((adicAlgebraMap J e.toAlgHom x).val n) =
    adicIdealQuotientMap _ _ e.toAlgHom _ n (adicRefinementQuotient _ _ id _ n (x.val n))
  rw [adicAlgebraMap_val]
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- The Chinese-remainder decomposition intertwines the original action and factor transport. -/
theorem finiteFiberCompletionEquiv_equivariant [Module.Finite R S] [IsNoetherianRing S]
    (J : Ideal R) [J.IsMaximal] (e : S ≃ₐ[R] S) (Q : J.primesOver S)
    (x : AdicCompletion (J.map (algebraMap R S)) S) :
    finiteFiberCompletionEquiv J (adicAlgebraMap J e.toAlgHom x) (fiberPrimeEquiv J e Q) =
      fiberCompletionTransport J e Q (finiteFiberCompletionEquiv J x Q) := by
  simp only [finiteFiberCompletionEquiv_apply]
  exact finiteFiberProjection_equivariant J e Q x

/-- Equivariance at a preserved point, expressed with one fixed target completion. -/
theorem finiteFiberProjection_equivariant_fixed (J : Ideal R) [J.IsMaximal]
    (f : S →ₐ[R] S) (Q : J.primesOver S) (h : Q.val.map f.toRingHom ≤ Q.val)
    (x : AdicCompletion (J.map (algebraMap R S)) S) :
    finiteFiberProjection J Q (adicAlgebraMap J f x) =
      adicIdealMap Q.val Q.val f h (finiteFiberProjection J Q x) := by
  apply Subtype.ext
  funext n
  change adicRefinementQuotient _ _ id _ n ((adicAlgebraMap J f x).val n) =
    adicIdealQuotientMap _ _ f h n (adicRefinementQuotient _ _ id _ n (x.val n))
  rw [adicAlgebraMap_val]
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

end CanonicalRoots
