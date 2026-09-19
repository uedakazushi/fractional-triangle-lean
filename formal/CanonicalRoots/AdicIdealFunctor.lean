import CanonicalRoots.AdicAlgebraFunctor

noncomputable section
namespace CanonicalRoots

variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]

/-- Quotient map for an algebra map carrying one ideal into another. -/
def adicIdealQuotientMap (I : Ideal S) (J : Ideal T) (f : S →ₐ[R] T)
    (h : I.map f.toRingHom ≤ J) (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Ideal S)) →ₐ[R] (T ⧸ (J ^ n • ⊤ : Ideal T)) :=
  Ideal.quotientMapₐ _ f (by
    simp only [Ideal.smul_eq_mul, Ideal.mul_top]
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact pow_le_pow_left' h n)

set_option backward.isDefEq.respectTransparency.types false in
/-- Functoriality for actual completions at possibly different ideals. -/
def adicIdealMap (I : Ideal S) (J : Ideal T) (f : S →ₐ[R] T)
    (h : I.map f.toRingHom ≤ J) : AdicCompletion I S →ₐ[R] AdicCompletion J T where
  toFun x := ⟨fun n => adicIdealQuotientMap I J f h n (x.val n), fun {m n} hmn => by
    change AdicCompletion.transitionMap J T hmn (adicIdealQuotientMap I J f h n (x.val n)) =
      adicIdealQuotientMap I J f h m (x.val m)
    rw [← x.property hmn]
    generalize x.val n = y
    induction y using Submodule.Quotient.induction_on with | _ y => rfl⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (adicIdealQuotientMap I J f h n) (x.val n) (y.val n)
  map_mul' x y := by
    apply Subtype.ext
    funext n
    exact map_mul (adicIdealQuotientMap I J f h n) (x.val n) (y.val n)
  commutes' r := by apply Subtype.ext; funext n; exact (adicIdealQuotientMap I J f h n).commutes r

@[simp] theorem adicIdealMap_val (I : Ideal S) (J : Ideal T) (f : S →ₐ[R] T)
    (h : I.map f.toRingHom ≤ J) (x : AdicCompletion I S) (n : ℕ) :
    (adicIdealMap I J f h x).val n = adicIdealQuotientMap I J f h n (x.val n) := rfl

@[simp] theorem adicIdealMap_id (I : Ideal S)
    (h : I.map (AlgHom.id R S).toRingHom ≤ I) :
    adicIdealMap I I (AlgHom.id R S) h = AlgHom.id R _ := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  funext n
  change adicIdealQuotientMap I I (AlgHom.id R S) h n (x.val n) = x.val n
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

theorem adicIdealMap_comp (I : Ideal S) (J : Ideal T) (K : Ideal U)
    (f : S →ₐ[R] T) (g : T →ₐ[R] U)
    (hf : I.map f.toRingHom ≤ J) (hg : J.map g.toRingHom ≤ K)
    (hgf : I.map (g.comp f).toRingHom ≤ K) :
    (adicIdealMap J K g hg).comp (adicIdealMap I J f hf) =
      adicIdealMap I K (g.comp f) hgf := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  funext n
  change adicIdealQuotientMap J K g hg n (adicIdealQuotientMap I J f hf n (x.val n)) =
    adicIdealQuotientMap I K (g.comp f) hgf n (x.val n)
  generalize x.val n = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- An algebra equivalence taking an ideal onto an ideal gives an equivalence of completions. -/
def adicIdealEquiv (I : Ideal S) (J : Ideal T) (e : S ≃ₐ[R] T)
    (h : I.map e.toRingHom = J) : AdicCompletion I S ≃ₐ[R] AdicCompletion J T := by
  have hi : J.map e.symm.toRingHom = I := by
    rw [← h, Ideal.map_map]
    simpa using congrArg (fun f : S →+* S => I.map f) e.symm_toRingHom_comp_toRingHom
  apply AlgEquiv.ofAlgHom (adicIdealMap I J e.toAlgHom h.le)
    (adicIdealMap J I e.symm.toAlgHom hi.le)
  · apply AlgHom.ext
    intro x
    apply Subtype.ext
    funext n
    change adicIdealQuotientMap I J e.toAlgHom h.le n
      (adicIdealQuotientMap J I e.symm.toAlgHom hi.le n (x.val n)) = x.val n
    generalize x.val n = y
    induction y using Submodule.Quotient.induction_on with
    | _ y => exact congrArg (Ideal.Quotient.mk _) (e.apply_symm_apply y)
  · apply AlgHom.ext
    intro x
    apply Subtype.ext
    funext n
    change adicIdealQuotientMap J I e.symm.toAlgHom hi.le n
      (adicIdealQuotientMap I J e.toAlgHom h.le n (x.val n)) = x.val n
    generalize x.val n = y
    induction y using Submodule.Quotient.induction_on with
    | _ y => exact congrArg (Ideal.Quotient.mk _) (e.symm_apply_apply y)

end CanonicalRoots
