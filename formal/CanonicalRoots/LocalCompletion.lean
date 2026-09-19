import CanonicalRoots.HypersurfaceNonregular
import Mathlib.RingTheory.AdicCompletion.Algebra

noncomputable section
namespace CanonicalRoots

variable {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S J] [IsLocalRing S]

/-- mathlib's local quotient isomorphisms, in the exact quotient format used by completion. -/
def localAdicQuotientEquiv (n : ℕ) :
    (R ⧸ (J ^ n • ⊤ : Ideal R)) ≃ₐ[R]
      (S ⧸ (IsLocalRing.maximalIdeal S ^ n • ⊤ : Ideal S)) :=
  (Ideal.quotientEquivAlgOfEq R (by simp : (J ^ n • ⊤ : Ideal R) = J ^ n)).trans
    ((IsLocalization.AtPrime.equivQuotMaximalIdealPow J S n).trans
      (Ideal.quotientEquivAlgOfEq R
        (by simp : (IsLocalRing.maximalIdeal S ^ n • ⊤ : Ideal S) =
          IsLocalRing.maximalIdeal S ^ n)).symm)

theorem localAdicQuotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : R ⧸ (J ^ n • ⊤ : Ideal R)) :
    AdicCompletion.transitionMap (IsLocalRing.maximalIdeal S) S h
      (localAdicQuotientEquiv J S n x) =
      localAdicQuotientEquiv J S m (AdicCompletion.transitionMap J R h x) := by
  induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- Completion at a maximal ideal agrees with completion of the actual localization. -/
def localCompletionEquiv :
    AdicCompletion J R ≃ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal S) S where
  toFun x := ⟨fun n => localAdicQuotientEquiv J S n (x.val n), fun h => by
    rw [localAdicQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n => (localAdicQuotientEquiv J S n).symm (x.val n), fun {m n} h => by
    apply (localAdicQuotientEquiv J S m).injective
    rw [← localAdicQuotientEquiv_transition]
    simp only [AlgEquiv.apply_symm_apply, x.property h]⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (localAdicQuotientEquiv J S n).symm_apply_apply (x.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (localAdicQuotientEquiv J S n).apply_symm_apply (x.val n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (localAdicQuotientEquiv J S n) (x.val n) (y.val n)
  map_mul' x y := by
    apply Subtype.ext
    funext n
    exact map_mul (localAdicQuotientEquiv J S n) (x.val n) (y.val n)
  commutes' r := by
    apply Subtype.ext
    funext n
    exact (localAdicQuotientEquiv J S n).commutes r

/-- In particular this applies to the kernel of every actual complex point. -/
def augmentationCompletionEquiv {A : Type*} [CommRing A] [Algebra ℂ A] (ε : A →ₐ[ℂ] ℂ) :
    AdicCompletion (RingHom.ker ε.toRingHom) A ≃ₐ[ℂ]
      AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing ε)) (AugmentationLocalRing ε) :=
  (localCompletionEquiv (RingHom.ker ε.toRingHom) (AugmentationLocalRing ε)).restrictScalars ℂ

end CanonicalRoots
