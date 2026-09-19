import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom

noncomputable section
namespace CanonicalRoots

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- The square-zero uniqueness API also applies to any surjective presentation of the quotient. -/
theorem formallyUnramified_comp_injective_of_surjective [Algebra.FormallyUnramified R A]
    (q : B →ₐ[R] C) (hq : Function.Surjective q) (hk : (RingHom.ker q.toRingHom) ^ 2 = ⊥) :
    Function.Injective (fun f : A →ₐ[R] B => q.comp f) := by
  intro f g h
  apply Algebra.FormallyUnramified.comp_injective (RingHom.ker q.toRingHom) hk
  apply AlgHom.ext
  intro a
  apply (Ideal.quotientKerAlgEquivOfSurjective hq).injective
  exact DFunLike.congr_fun h a

/-- Adjacent positive powers have a square-zero transition kernel. -/
theorem ideal_power_transition_ker_sq (I : Ideal B) (n : ℕ) :
    (RingHom.ker (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))).toRingHom) ^ 2 = ⊥ := by
  change (RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))) ^ 2 = ⊥
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  exact eq_bot_mono (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)))
    (Ideal.map_quotient_self _)

/-- For a formally unramified algebra, a map into any finite infinitesimal thickening
is determined by its reduction to the initial quotient. -/
theorem formallyUnramified_power_comp_injective [Algebra.FormallyUnramified R A]
    (I : Ideal B) (n : ℕ) :
    Function.Injective (fun f : A →ₐ[R] B ⧸ I ^ (n + 1) =>
      (Ideal.Quotient.factorₐ R (show I ^ (n + 1) ≤ I from Ideal.pow_le_self (by omega))).comp f) := by
  induction n with
  | zero =>
    intro f g h
    apply AlgHom.ext
    intro a
    apply (Ideal.quotientEquivAlgOfEq R (by simp : I ^ (0 + 1) = I)).injective
    exact DFunLike.congr_fun h a
  | succ n ih =>
    intro f g h
    let q := Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))
    apply formallyUnramified_comp_injective_of_surjective q
      (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))
      (ideal_power_transition_ker_sq I n)
    apply ih
    simpa only [q, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp] using h

set_option backward.isDefEq.respectTransparency.types false in
theorem adic_factor_evalOne (I : Ideal B) (n : ℕ) (x : AdicCompletion I B) :
    Ideal.Quotient.factorₐ R (show I ^ (n + 1) ≤ I from Ideal.pow_le_self (by omega))
      (AdicCompletion.evalₐ I (n + 1) x) = AdicCompletion.evalOneₐ I x := by
  unfold AdicCompletion.evalOneₐ AdicCompletion.evalₐ
  change Ideal.Quotient.factorₐ R (Ideal.pow_le_self (by omega))
      (Ideal.quotientEquivAlgOfEq B (by simp) (x.val (n + 1))) =
    Ideal.Quotient.factorₐ B (by simp) (Ideal.quotientEquivAlgOfEq B (by simp) (x.val 1))
  rw [← x.property (show 1 ≤ n + 1 by omega)]
  generalize x.val (n + 1) = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- Formal unramifiedness gives uniqueness of a map into an actual adic completion
from its initial residue map, without a Noetherian or finite-presentation assumption. -/
theorem formallyUnramified_adicCompletion_comp_injective [Algebra.FormallyUnramified R A]
    (I : Ideal B) :
    Function.Injective (fun f : A →ₐ[R] AdicCompletion I B =>
      ((AdicCompletion.evalOneₐ I).restrictScalars R).comp f) := by
  intro f g h
  apply AlgHom.ext
  intro a
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
    have : Subsingleton (B ⧸ I ^ 0) := by simp
    exact Subsingleton.elim _ _
  | succ n =>
    have he : ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R).comp f =
        ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R).comp g := by
      apply formallyUnramified_power_comp_injective I n
      apply AlgHom.ext
      intro x
      change Ideal.Quotient.factorₐ R (Ideal.pow_le_self (by omega))
          (AdicCompletion.evalₐ I (n + 1) (f x)) =
        Ideal.Quotient.factorₐ R (Ideal.pow_le_self (by omega))
          (AdicCompletion.evalₐ I (n + 1) (g x))
      rw [adic_factor_evalOne, adic_factor_evalOne]
      exact DFunLike.congr_fun h x
    exact DFunLike.congr_fun he a

/-- The formal étale lifting property extends from square-zero thickenings to actual completion. -/
theorem formallyEtale_adicCompletion_comp_bijective [Algebra.FormallyEtale R A] (I : Ideal B) :
    Function.Bijective (fun f : A →ₐ[R] AdicCompletion I B =>
      ((AdicCompletion.evalOneₐ I).restrictScalars R).comp f) :=
  ⟨formallyUnramified_adicCompletion_comp_injective I,
    fun f => Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f⟩

end CanonicalRoots
