import CanonicalRoots

noncomputable section
open CanonicalRoots MvPolynomial

-- The full chart uses only a positive eliminated exponent and a nonzero coordinate,
-- with no smoothness, formal-etaleness, or assumed isomorphism hypothesis.
example {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)
    (hv : ∑ i, v i ^ p i = 0) (hp : 0 < p 0) (hv0 : v 0 ≠ 0) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (AugmentationLocalRing (fermatPoint p v hv)))
      (AugmentationLocalRing (fermatPoint p v hv)) ≃ₐ[ℂ] FermatTailCompletion v) :=
  ⟨fermatLocalCompletedChartEquiv p v hv hp hv0⟩

example {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)
    (hv : ∑ i, v i ^ p i = 0) (hp : 0 < p 0) (hv0 : v 0 ≠ 0)
    (x : FermatPointCompletion p v hv) :
    fermatTailCompletedInclusion p v hv (fermatCompletedChart p v hv hp hv0 x) = x :=
  DFunLike.congr_fun (fermatTailCompletedInclusion_comp_chart p v hv hp hv0) x

example {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)
    (hv : ∑ i, v i ^ p i = 0) (hp : 0 < p 0) (hv0 : v 0 ≠ 0)
    (x : FermatTailCompletion v) :
    fermatCompletedChart p v hv hp hv0 (fermatTailCompletedInclusion p v hv x) = x :=
  DFunLike.congr_fun (fermatCompletedChart_comp_tail p v hv hp hv0) x

example : Nonempty (FermatPointCompletion ![2, 3, 5] ![1, -1, 0]
    (by norm_num [Fin.sum_univ_succ]) ≃ₐ[ℂ] FermatTailCompletion ![1, -1, 0]) := by
  exact ⟨fermatCompletedChartEquiv ![2, 3, 5] ![1, -1, 0]
    (by norm_num [Fin.sum_univ_succ]) (by norm_num) (by norm_num)⟩

-- Recover the eliminated coordinate as an equality in the actual completion.
example {n : ℕ} (p : Fin (n + 1) → ℕ) (v : Fin (n + 1) → ℂ)
    (hv : ∑ i, v i ^ p i = 0) (hp : 0 < p 0) (hv0 : v 0 ≠ 0) :
    (fermatCompletedChartEquiv p v hv hp hv0).symm (fermatCompletedBranch p v hp hv hv0) =
      algebraMap (AmbientRing p) (FermatPointCompletion p v hv) (ambientQuotient p (X 0)) :=
  fermatTailCompletedInclusion_branch p v hv hp hv0
