import Mathlib.RingTheory.AdicCompletion.Functoriality

noncomputable section
namespace CanonicalRoots

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

/-- The two quotient systems for I-adic S as an R-module and IS-adic S as a ring. -/
def adicScalarQuotientEquiv (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃ₗ[R]
      (S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S S)) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    simp)).trans (Submodule.Quotient.restrictScalarsEquiv R _)

@[simp] theorem adicScalarQuotientEquiv_mk (n : ℕ) (s : S) :
    adicScalarQuotientEquiv I n (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := rfl

theorem adicScalarQuotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S h
      (adicScalarQuotientEquiv I n x) =
      adicScalarQuotientEquiv I m (AdicCompletion.transitionMap I S h x) := by
  induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- Change from completion as a module over R to completion at the extended ideal of S. -/
def adicScalarExtensionEquiv :
    AdicCompletion I S ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := ⟨fun n => adicScalarQuotientEquiv I n (x.val n), fun h => by
    rw [adicScalarQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n => (adicScalarQuotientEquiv I n).symm (x.val n), fun {m n} h => by
    apply (adicScalarQuotientEquiv I m).injective
    rw [← adicScalarQuotientEquiv_transition]
    simp only [LinearEquiv.apply_symm_apply, x.property h]⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (adicScalarQuotientEquiv I n).symm_apply_apply (x.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (adicScalarQuotientEquiv I n).apply_symm_apply (x.val n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (adicScalarQuotientEquiv I n) (x.val n) (y.val n)
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact map_smul (adicScalarQuotientEquiv I n) r (x.val n)

@[simp] theorem adicScalarExtensionEquiv_of (s : S) :
    adicScalarExtensionEquiv I (AdicCompletion.of I S s) =
      AdicCompletion.of (I.map (algebraMap R S)) S s := rfl

end CanonicalRoots
