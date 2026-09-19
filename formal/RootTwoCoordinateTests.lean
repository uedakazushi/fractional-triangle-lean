import CanonicalRoots.RootTwoCoordinateNonregular

noncomputable section
open CanonicalRoots

-- The conclusion is nonregularity of the original local root ring, not a separate cyclic model.
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
    (v : Fin (n + 1) → ℂ) (hv : ∑ l, v l ^ p l = 0)
    (i j : Fin n) (hij : i ≠ j) (hi : v i.succ = 0) (hj : v j.succ = 0)
    (hz : ∀ l, l ≠ i.succ → l ≠ j.succ → v l ≠ 0)
    (hs : 2 ≤ Nat.gcd (p i.succ) (p j.succ)) :
    rootPoint p τ (fermatPoint p v hv) ≠
      rootOriginPoint p (fun k => lt_of_lt_of_le (by decide) (hp.1 k)) τ ∧
    ¬ IsRegularLocalRing (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) :=
  rootTwoCoordinate_nonorigin_nonregular p τ hp ha hτ v hv i j hij hi hj hz hs

-- A concrete admissible four-variable root: a=1 and signature (4,6,6,5).
-- The actual Fermat point (1,0,0,-1) has a nonregular image in the root ring.
example : ∃ z : AmbientRing ![4, 6, 6, 5] →ₐ[ℂ] ℂ,
    ¬ IsRegularLocalRing (AugmentationLocalRing
      (rootPoint ![4, 6, 6, 5] (omegaDegree ![4, 6, 6, 5]) z)) := by
  let p : Fin 4 → ℕ := ![4, 6, 6, 5]
  let v : Fin 4 → ℂ := ![1, 0, 0, -1]
  have hp : AdmissibleSignature p := by
    constructor
    · intro k; fin_cases k <;> norm_num [p]
    · norm_num [p, Fin.sum_univ_succ]
  have hv : ∑ l, v l ^ p l = 0 := by norm_num [p, v, Fin.sum_univ_succ]
  refine ⟨fermatPoint p v hv, ?_⟩
  apply rootTwoCoordinate_not_regular p (omegaDegree p) hp (a := 1) (by decide)
    (by simp [IsCanonicalRoot]) v hv (0 : Fin 3) 1 (by decide) (by norm_num [v]) (by norm_num [v])
  · intro l hli hlj
    fin_cases l <;> norm_num [v] at *
  · norm_num [p]
