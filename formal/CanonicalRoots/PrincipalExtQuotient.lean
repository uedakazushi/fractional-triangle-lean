import CanonicalRoots.PrincipalExtScalars

noncomputable section
namespace CanonicalRoots

universe u
variable {R : Type u} [CommRing R] [IsDomain R]

/-- The quotient action transported through the computed Ext isomorphism.
The following theorem verifies that this is the descent of the original R-action. -/
def principalExtQuotientModule (f : R) (hf : f ≠ 0) :
    Module (R ⧸ Ideal.span {f}) (PrincipalExt f) :=
  (principalExtEquiv f hf).symm.toAddEquiv.module (R ⧸ Ideal.span {f})

def principalExtQuotientEquiv (f : R) (hf : f ≠ 0) :
    letI := principalExtQuotientModule f hf
    (R ⧸ Ideal.span {f}) ≃ₗ[R ⧸ Ideal.span {f}] PrincipalExt f :=
  ((principalExtEquiv f hf).symm.toAddEquiv.linearEquiv (R ⧸ Ideal.span {f})).symm

theorem principalExtQuotient_smul (f : R) (hf : f ≠ 0) (r : R) (x : PrincipalExt f) :
    letI := principalExtQuotientModule f hf
    Ideal.Quotient.mk (Ideal.span {f}) r • x = r • x := by
  letI := principalExtQuotientModule f hf
  change principalExtEquiv f hf
    (Ideal.Quotient.mk (Ideal.span {f}) r * (principalExtEquiv f hf).symm x) = r • x
  change principalExtEquiv f hf (r • (principalExtEquiv f hf).symm x) = r • x
  rw [map_smul, LinearEquiv.apply_symm_apply]

theorem principalExtQuotient_free (f : R) (hf : f ≠ 0) :
    letI := principalExtQuotientModule f hf
    Module.Free (R ⧸ Ideal.span {f}) (PrincipalExt f) := by
  letI := principalExtQuotientModule f hf
  exact Module.Free.of_equiv (principalExtQuotientEquiv f hf)

end CanonicalRoots
