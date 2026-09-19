import CanonicalRoots.PrincipalExt

noncomputable section
namespace CanonicalRoots
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u v
variable (K : Type v) [CommRing K] {R : Type u} [CommRing R] [Algebra K R] [IsDomain R]

theorem principalExt_smul_algebraMap (f : R) (k : K) (x : PrincipalExt f) :
    k • x = (algebraMap K R k) • x := by
  rw [Ext.smul_eq_comp_mk₀, Ext.smul_eq_comp_mk₀]
  rfl

def principalBoundaryOfAlgebra (f : R) (hf : f ≠ 0) : R →ₗ[K] PrincipalExt f where
  toFun := principalBoundary f hf
  map_add' := (principalBoundary f hf).map_add
  map_smul' k x := by
    rw [Algebra.smul_def, principalExt_smul_algebraMap]
    exact (principalBoundary f hf).map_smul (algebraMap K R k) x

theorem principalBoundaryOfAlgebra_apply (f : R) (hf : f ≠ 0) (x : R) :
    principalBoundaryOfAlgebra K f hf x = principalBoundary f hf x := rfl

def principalExtEquivOfAlgebra (f : R) (hf : f ≠ 0) :
    (R ⧸ Ideal.span {f}) ≃ₗ[K] PrincipalExt f where
  toAddEquiv := (principalExtEquiv f hf).toAddEquiv
  map_smul' k x := by
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective x
    change principalExtEquiv f hf (k • Ideal.Quotient.mk (Ideal.span {f}) r) =
      k • principalExtEquiv f hf (Ideal.Quotient.mk (Ideal.span {f}) r)
    have hm : Ideal.Quotient.mk (Ideal.span {f}) (k • r) =
        k • Ideal.Quotient.mk (Ideal.span {f}) r :=
      (Ideal.Quotient.mkₐ K (Ideal.span {f})).toLinearMap.map_smul k r
    rw [← hm, principalExtEquiv_mk, principalExtEquiv_mk]
    exact (principalBoundaryOfAlgebra K f hf).map_smul k r

theorem principalExtEquivOfAlgebra_mk (f : R) (hf : f ≠ 0) (x : R) :
    principalExtEquivOfAlgebra K f hf (Ideal.Quotient.mk (Ideal.span {f}) x) =
      principalBoundaryOfAlgebra K f hf x := rfl

end CanonicalRoots
