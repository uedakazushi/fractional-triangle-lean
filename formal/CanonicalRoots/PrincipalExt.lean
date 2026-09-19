import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
namespace CanonicalRoots
open CategoryTheory CategoryTheory.Abelian

universe u
variable {R : Type u} [CommRing R]

/-- The standard principal-quotient presentation by two free modules. -/
abbrev principalShortComplex (f : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.mulLeft R f)
    (Ideal.Quotient.mkₐ R (Ideal.span {f})).toLinearMap (by
      ext x
      simp [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem])

theorem principalShortComplex_shortExact [IsDomain R] (f : R) (hf : f ≠ 0) :
    (principalShortComplex f).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change Ideal.Quotient.mk (Ideal.span {f}) x = 0 ↔ ∃ y, f * y = x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact exists_congr (fun y => eq_comm)
  · exact mul_right_injective₀ hf
  · exact Ideal.Quotient.mk_surjective

abbrev PrincipalExt (f : R) :=
  Ext (ModuleCat.of R (R ⧸ Ideal.span {f})) (ModuleCat.of R R) 1

/-- Evaluation at one identifies Ext⁰ of a rank-one free module with the coefficient ring. -/
def freeExtZeroEquiv (R : Type u) [CommRing R] :
    Ext (ModuleCat.of R R) (ModuleCat.of R R) 0 ≃ₗ[R] R :=
  Ext.linearEquiv₀.trans (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R R))

theorem freeExtZeroEquiv_mk₀ (g : ModuleCat.of R R ⟶ ModuleCat.of R R) :
    freeExtZeroEquiv R (Ext.mk₀ g) = g 1 := by
  exact congrArg (fun h : ModuleCat.of R R ⟶ ModuleCat.of R R => h 1)
    ((Ext.linearEquiv₀ (R := R)).apply_symm_apply g)

theorem freeExtZeroEquiv_precomp (f : R)
    (e : Ext (ModuleCat.of R R) (ModuleCat.of R R) 0) :
    freeExtZeroEquiv R ((Ext.mk₀ (principalShortComplex f).f).comp e (zero_add 0)) =
      f * freeExtZeroEquiv R e := by
  obtain ⟨g,rfl⟩ := Ext.homEquiv₀.symm.surjective e
  change freeExtZeroEquiv R ((Ext.mk₀ (principalShortComplex f).f).comp (Ext.mk₀ g) (zero_add 0)) =
    f * freeExtZeroEquiv R (Ext.mk₀ g)
  rw [Ext.mk₀_comp_mk₀, freeExtZeroEquiv_mk₀, freeExtZeroEquiv_mk₀]
  change g (f * 1) = f * g 1
  simpa only [smul_eq_mul] using g.hom.map_smul f (1 : R)

def principalBoundary [IsDomain R] (f : R) (hf : f ≠ 0) : R →ₗ[R] PrincipalExt f :=
  ((principalShortComplex_shortExact f hf).extClass.precompOfLinear R (ModuleCat.of R R)
    (show 1 + 0 = 1 from rfl)).comp (freeExtZeroEquiv R).symm.toLinearMap

theorem principalBoundary_surjective [IsDomain R] (f : R) (hf : f ≠ 0) :
    Function.Surjective (principalBoundary f hf) := by
  intro x
  obtain ⟨e,he⟩ := Ext.contravariant_sequence_exact₃ (principalShortComplex_shortExact f hf)
    (ModuleCat.of R R) x (Ext.eq_zero_of_projective _) (show 1 + 0 = 1 from rfl)
  refine ⟨freeExtZeroEquiv R e,?_⟩
  change (principalShortComplex_shortExact f hf).extClass.comp
    ((freeExtZeroEquiv R).symm (freeExtZeroEquiv R e)) (show 1 + 0 = 1 from rfl) = x
  rw [LinearEquiv.symm_apply_apply]
  exact he

theorem principalBoundary_ker [IsDomain R] (f : R) (hf : f ≠ 0) :
    LinearMap.ker (principalBoundary f hf) = (Ideal.span {f}).restrictScalars R := by
  ext r
  change principalBoundary f hf r = 0 ↔ r ∈ Ideal.span {f}
  constructor
  · intro hr
    obtain ⟨e,he⟩ := Ext.contravariant_sequence_exact₁ (principalShortComplex_shortExact f hf)
      (ModuleCat.of R R) ((freeExtZeroEquiv R).symm r) (show 1 + 0 = 1 from rfl) hr
    have he' := congrArg (freeExtZeroEquiv R) he
    rw [freeExtZeroEquiv_precomp, LinearEquiv.apply_symm_apply] at he'
    exact Ideal.mem_span_singleton.mpr ⟨freeExtZeroEquiv R e,he'.symm⟩
  · intro hr
    obtain ⟨s,hs⟩ := Ideal.mem_span_singleton.mp hr
    subst r
    have he : (freeExtZeroEquiv R).symm (f * s) =
        (Ext.mk₀ (principalShortComplex f).f).comp ((freeExtZeroEquiv R).symm s) (zero_add 0) := by
      apply (freeExtZeroEquiv R).injective
      rw [freeExtZeroEquiv_precomp, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change (principalShortComplex_shortExact f hf).extClass.comp
      ((freeExtZeroEquiv R).symm (f * s)) (show 1 + 0 = 1 from rfl) = 0
    rw [he]
    exact (principalShortComplex_shortExact f hf).extClass_comp_assoc _

/-- Ext¹ of a hypersurface, computed from its actual free presentation. -/
def principalExtEquiv [IsDomain R] (f : R) (hf : f ≠ 0) :
    (R ⧸ Ideal.span {f}) ≃ₗ[R] PrincipalExt f :=
  (Submodule.quotEquivOfEq _ _ (principalBoundary_ker f hf).symm).trans
    ((principalBoundary f hf).quotKerEquivOfSurjective (principalBoundary_surjective f hf))

theorem principalExtEquiv_mk [IsDomain R] (f : R) (hf : f ≠ 0) (x : R) :
    principalExtEquiv f hf (Ideal.Quotient.mk (Ideal.span {f}) x) = principalBoundary f hf x := by
  rfl

end CanonicalRoots
