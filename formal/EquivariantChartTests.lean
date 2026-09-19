import CanonicalRoots

noncomputable section
open CanonicalRoots

-- The actual coordinate isomorphism commutes with every original stabilizer element.
example {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0) (hp0 : 0 < p 0) (hv0 : v 0 ≠ 0)
    (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (x : FermatPointCompletion p v hv) :
    fermatCompletedChartEquiv p v hv hp0 hv0 (pointCompletedCharacterHom p τ (fermatPoint p v hv) χ x) =
      fermatTailCompletedCharacterAction p τ v hv χ (fermatCompletedChartEquiv p v hv hp0 hv0 x) :=
  fermatCompletedChartEquiv_equivariant p τ v hv hp0 hv0 χ x

-- No finite-action, fixed-ring, smoothness or classification assumption is added to this signature.
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
    (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0) (hv0 : v 0 ≠ 0) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) ≃+*
        fermatTailCompletedFixed p τ v hv) :=
  ⟨rootFermatCompletedInvariantChartEquiv p τ hp ha hτ v hv hv0⟩

example {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0)
    (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (x : FermatTailCompletion v) :
    fermatTailCompletedCharacterAction p τ v hv χ⁻¹
      (fermatTailCompletedCharacterAction p τ v hv χ x) = x := by
  have h := (fermatTailCompletedCharacterAction p τ v hv).map_mul χ⁻¹ χ
  rw [inv_mul_cancel, map_one] at h
  exact (DFunLike.congr_fun h x).symm
