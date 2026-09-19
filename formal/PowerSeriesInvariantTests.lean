import CanonicalRoots

noncomputable section
open CanonicalRoots

-- Arbitrary-point coordinates are equivariant for every diagonal substitution fixing that point.
example {n : ℕ} (v w : Fin n → ℂ) (hv : ∀ i, w i * v i = v i)
    (x : AdicCompletion (RingHom.ker (polynomialPoint v).toRingHom) (MvPolynomial (Fin n) ℂ)) :
    polynomialPointCompletionEquiv v (polynomialCompletedDiagonal v w hv x) =
      MvPowerSeries.rescaleAlgHom w (polynomialPointCompletionEquiv v x) :=
  polynomialPointCompletionEquiv_diagonal v w hv x

-- For a nontrivial cyclic action, the mixed invariant survives modulo the square of the origin ideal.
example (s : ℕ) (hs : 2 ≤ s) :
    DiagonalIndecomposableExponent (cyclicFormalWeights s (0 : Fin 4) 1)
      (Finsupp.single 0 1 + Finsupp.single 1 1) :=
  cyclicFormalIndecomposable_mixed s 0 1 hs (by decide)

-- Additional fixed coordinates contribute independent directions, regardless of their position.
example (s : ℕ) (hs : 2 ≤ s) :
    DiagonalIndecomposableExponent (cyclicFormalWeights s (0 : Fin 4) 1) (Finsupp.single 3 1) :=
  cyclicFormalIndecomposable_extra s 0 1 (by omega) (by decide) 3 (by decide) (by decide)

-- The finite-dimensionality needed for the actual root-ring bound is a conclusion, not an assumption.
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ) (hv0 : v 0 ≠ 0) :
    Module.Finite ℂ (powerSeriesDiagonalOriginIdeal (fermatTailWeights p τ v hv)).Cotangent :=
  rootFormal_cotangent_finite p τ v hv hp ha hτ hv0

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (v : Fin (n + 1) → ℂ) (hv : ∑ i, v i ^ p i = 0)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ) (hv0 : v 0 ≠ 0) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
      (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) ≃+*
        powerSeriesDiagonalFixed (fermatTailWeights p τ v hv)) :=
  ⟨rootFermatPowerSeriesInvariantEquiv p τ v hv hp ha hτ hv0⟩
