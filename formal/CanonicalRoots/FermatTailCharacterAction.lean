import CanonicalRoots.FermatCompletedChartEquiv
import CanonicalRoots.RootPointCompletion
import CanonicalRoots.AdicAutomorphismAction

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)

def fermatTailCharacterHom (χ : RootCharacter p τ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (fun i => rootCharacterValue p τ χ (xDegree p i.succ) • X i)

@[simp] theorem fermatTailCharacterHom_X (χ : RootCharacter p τ) (i : Fin n) :
    fermatTailCharacterHom p τ χ (X i) = rootCharacterValue p τ χ (xDegree p i.succ) • X i :=
  aeval_X _ _

theorem fermatTailCharacterHom_one : fermatTailCharacterHom p τ 1 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [fermatTailCharacterHom_X, rootCharacterValue_one, one_smul, AlgHom.id_apply]

theorem fermatTailCharacterHom_mul (χ ψ : RootCharacter p τ) :
    fermatTailCharacterHom p τ (χ * ψ) =
      (fermatTailCharacterHom p τ χ).comp (fermatTailCharacterHom p τ ψ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, fermatTailCharacterHom_X, map_smul, rootCharacterValue_mul,
    smul_smul, mul_comm]

def fermatTailCharacterEquiv (χ : RootCharacter p τ) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  AlgEquiv.ofAlgHom (fermatTailCharacterHom p τ χ) (fermatTailCharacterHom p τ χ⁻¹)
    (by rw [← fermatTailCharacterHom_mul, mul_inv_cancel χ, fermatTailCharacterHom_one])
    (by rw [← fermatTailCharacterHom_mul, inv_mul_cancel χ, fermatTailCharacterHom_one])

def fermatTailCharacterAction : RootCharacter p τ →*
    (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) where
  toFun := fermatTailCharacterEquiv p τ
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact fermatTailCharacterHom_one p τ
  map_mul' χ ψ := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact fermatTailCharacterHom_mul p τ χ ψ

theorem fermatTailInclusion_equivariant (χ : RootCharacter p τ) :
    (ambientCharacterHom p τ χ).comp (fermatTailInclusion p) =
      (fermatTailInclusion p).comp (fermatTailCharacterHom p τ χ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, fermatTailInclusion, aeval_X, ambientCharacterHom_X, map_smul,
    fermatTailCharacterHom_X]

variable (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0)

/-- The point stabilizer preserves the tail-coordinate point. -/
theorem fermatTailPoint_stabilized (χ : rootPointStabilizer p τ (fermatPoint p v hv)) :
    (fermatTailPoint v).comp (fermatTailCharacterHom p τ χ.val) = fermatTailPoint v := by
  apply MvPolynomial.algHom_ext
  intro i
  have h := (mem_rootPointStabilizer_iff_coordinates p τ (fermatPoint p v hv) χ.val).mp χ.property i.succ
  simpa only [AlgHom.comp_apply, fermatTailCharacterHom_X, map_smul, fermatTailPoint, aeval_X,
    smul_eq_mul, fermatPoint_X] using h

theorem fermatTailCharacter_map_pointIdeal (χ : rootPointStabilizer p τ (fermatPoint p v hv)) :
    (RingHom.ker (fermatTailPoint v).toRingHom).map (fermatTailCharacterEquiv p τ χ.val).toRingHom =
      RingHom.ker (fermatTailPoint v).toRingHom :=
  (augmentation_map_kernel_iff (fermatTailPoint v) (fermatTailCharacterEquiv p τ χ.val)).mpr
    (fermatTailPoint_stabilized p τ v hv χ)

/-- The original stabilizer acts on the actual completion of the tail polynomial ring. -/
def fermatTailCompletedCharacterAction : rootPointStabilizer p τ (fermatPoint p v hv) →*
    (FermatTailCompletion v ≃ₐ[ℂ] FermatTailCompletion v) :=
  adicIdealAction _ ((fermatTailCharacterAction p τ).comp (rootPointStabilizer p τ (fermatPoint p v hv)).subtype)
    (fun χ => (fermatTailCharacter_map_pointIdeal p τ v hv χ).le)

/-- The same stabilizer acts on the actual completed Fermat point ring. -/
def fermatPointCompletedCharacterAction : rootPointStabilizer p τ (fermatPoint p v hv) →*
    (FermatPointCompletion p v hv ≃ₐ[ℂ] FermatPointCompletion p v hv) :=
  adicIdealAction _ ((ambientCharacterAction p τ).comp (rootPointStabilizer p τ (fermatPoint p v hv)).subtype)
    (fun χ => ((augmentation_map_kernel_iff (fermatPoint p v hv)
      (ambientCharacterEquiv p τ χ.val)).mpr χ.property).le)

@[simp] theorem fermatPointCompletedCharacterAction_apply
    (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (x : FermatPointCompletion p v hv) :
    fermatPointCompletedCharacterAction p τ v hv χ x =
      pointCompletedCharacterHom p τ (fermatPoint p v hv) χ x := rfl

end CanonicalRoots
