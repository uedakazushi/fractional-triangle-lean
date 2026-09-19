import CanonicalRoots.FermatTailCharacterAction
import CanonicalRoots.AdicIdealNaturality

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0)

theorem fermatTailCompletedInclusion_equivariant
    (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (x : FermatTailCompletion v) :
    fermatTailCompletedInclusion p v hv (fermatTailCompletedCharacterAction p τ v hv χ x) =
      fermatPointCompletedCharacterAction p τ v hv χ (fermatTailCompletedInclusion p v hv x) := by
  have h := adicIdealMap_square
    (RingHom.ker (fermatTailPoint v).toRingHom) (RingHom.ker (fermatPoint p v hv).toRingHom)
    (RingHom.ker (fermatTailPoint v).toRingHom) (RingHom.ker (fermatPoint p v hv).toRingHom)
    (fermatTailInclusion p) (fermatTailCharacterHom p τ χ.val)
    (ambientCharacterHom p τ χ.val) (fermatTailInclusion p)
    (fermatTailInclusion_map_pointIdeal p v hv)
    (fermatTailCharacter_map_pointIdeal p τ v hv χ).le
    ((augmentation_map_kernel_iff (fermatPoint p v hv)
      (ambientCharacterEquiv p τ χ.val)).mpr χ.property).le
    (fermatTailInclusion_map_pointIdeal p v hv) (fermatTailInclusion_equivariant p τ χ.val)
  exact (DFunLike.congr_fun h x).symm

variable (hp : 0 < p 0) (hv0 : v 0 ≠ 0)

/-- The proved formal-coordinate isomorphism intertwines the actual point stabilizer actions. -/
theorem fermatCompletedChartEquiv_equivariant
    (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (x : FermatPointCompletion p v hv) :
    fermatCompletedChartEquiv p v hv hp hv0 (fermatPointCompletedCharacterAction p τ v hv χ x) =
      fermatTailCompletedCharacterAction p τ v hv χ (fermatCompletedChartEquiv p v hv hp hv0 x) := by
  apply (fermatCompletedChartEquiv p v hv hp hv0).symm.injective
  change fermatTailCompletedInclusion p v hv
      (fermatCompletedChart p v hv hp hv0 (fermatPointCompletedCharacterAction p τ v hv χ x)) =
    fermatTailCompletedInclusion p v hv
      (fermatTailCompletedCharacterAction p τ v hv χ (fermatCompletedChart p v hv hp hv0 x))
  rw [fermatTailCompletedInclusion_equivariant]
  exact (DFunLike.congr_fun (fermatTailCompletedInclusion_comp_chart p v hv hp hv0) _).trans
    (congrArg (fermatPointCompletedCharacterAction p τ v hv χ)
      (DFunLike.congr_fun (fermatTailCompletedInclusion_comp_chart p v hv hp hv0) x)).symm

/-- Actual invariant elements of the completed tail-coordinate algebra. -/
def fermatTailCompletedFixed : Subalgebra ℂ (FermatTailCompletion v) where
  carrier := {x | ∀ χ : rootPointStabilizer p τ (fermatPoint p v hv),
    fermatTailCompletedCharacterAction p τ v hv χ x = x}
  algebraMap_mem' c χ := (fermatTailCompletedCharacterAction p τ v hv χ).commutes c
  zero_mem' χ := map_zero _
  one_mem' χ := map_one _
  add_mem' hx hy χ := by rw [map_add, hx χ, hy χ]
  mul_mem' hx hy χ := by rw [map_mul, hx χ, hy χ]

/-- Restrict the equivariant chart to the full stabilizer fixed rings. -/
def fermatPointFixedChartEquiv :
    pointCompletedFixed p τ (fermatPoint p v hv) ≃+* fermatTailCompletedFixed p τ v hv where
  toFun x := ⟨fermatCompletedChartEquiv p v hv hp hv0 x.val, fun χ => by
    rw [← fermatCompletedChartEquiv_equivariant, fermatPointCompletedCharacterAction_apply,
      x.property χ]⟩
  invFun x := ⟨(fermatCompletedChartEquiv p v hv hp hv0).symm x.val, fun χ => by
    change fermatPointCompletedCharacterAction p τ v hv χ (fermatTailCompletedInclusion p v hv x.val) =
      fermatTailCompletedInclusion p v hv x.val
    rw [← fermatTailCompletedInclusion_equivariant, x.property χ]⟩
  left_inv x := Subtype.ext ((fermatCompletedChartEquiv p v hv hp hv0).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((fermatCompletedChartEquiv p v hv hp hv0).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((fermatCompletedChartEquiv p v hv hp hv0).map_add x.val y.val)
  map_mul' x y := Subtype.ext ((fermatCompletedChartEquiv p v hv hp hv0).map_mul x.val y.val)

end CanonicalRoots
