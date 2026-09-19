import CanonicalRoots.FermatCyclicWeights
import CanonicalRoots.CyclicCotangentGenerators
import CanonicalRoots.RootPointOrigin

noncomputable section
namespace CanonicalRoots
open IsLocalRing

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
  (v : Fin (n + 1) → ℂ) (hv : ∑ l, v l ^ p l = 0)
  (i j : Fin n) (hij : i ≠ j) (hi : v i.succ = 0) (hj : v j.succ = 0)
  (hz : ∀ l, l ≠ i.succ → l ≠ j.succ → v l ≠ 0)
  (hs : 2 ≤ Nat.gcd (p i.succ) (p j.succ))

include hp ha hτ hij hi hj hz hs in
/-- The original root local ring has at least n+1 cotangent directions at the two-coordinate stratum. -/
theorem rootTwoCoordinate_cotangent_lowerBound :
    n + 1 ≤ Module.finrank (ResidueField (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
      (CotangentSpace (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv)))) := by
  let s := Nat.gcd (p i.succ) (p j.succ)
  have hd (t : Option (Fin n)) :
      DiagonalIndecomposableExponent (fermatTailWeights p τ v hv) (cyclicGeneratorExponent s i j t) :=
    (fermatIndecomposableExponent_iff_cyclic p τ hp ha hτ v hv i j hij hi hj hz _).mpr
      (cyclicGeneratorExponent_indecomposable s i j hs hij t)
  have h := rootPointLocal_cotangent_ge_of_monomials p τ v hv hp ha hτ
    (hz 0 (Ne.symm (Fin.succ_ne_zero i)) (Ne.symm (Fin.succ_ne_zero j))) (cyclicGeneratorExponent s i j) hd
    (cyclicGeneratorExponent_injective s i j (by omega) hij)
  simpa only [Fintype.card_option, Fintype.card_fin] using h

include hp ha hτ hij hi hj hz hs in
/-- A nontrivial two-coordinate stabilizer forces the actual root local ring to be nonregular. -/
theorem rootTwoCoordinate_not_regular :
    ¬ IsRegularLocalRing (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) := by
  let : IsNoetherianRing (RootRing p τ) := canonicalRoot_noetherian p hp ha τ hτ
  intro hreg
  let : IsRegularLocalRing (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) := hreg
  have he := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv)))).mp hreg
  have hdim := rootPointLocal_krullDim_le p τ hp ha hτ (fermatPoint p v hv)
  rw [← he] at hdim
  have hle : Module.finrank (ResidueField (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))))
      (CotangentSpace (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv)))) ≤ n := by
    exact_mod_cast hdim
  have hlt := rootTwoCoordinate_cotangent_lowerBound p τ hp ha hτ v hv i j hij hi hj hz hs
  omega

include hp ha hτ hij hi hj hz hs in
/-- The nonregular point lies away from the original graded root origin. -/
theorem rootTwoCoordinate_nonorigin_nonregular :
    rootPoint p τ (fermatPoint p v hv) ≠
      rootOriginPoint p (fun k => lt_of_lt_of_le (by decide) (hp.1 k)) τ ∧
    ¬ IsRegularLocalRing (AugmentationLocalRing (rootPoint p τ (fermatPoint p v hv))) := by
  refine ⟨rootPoint_ne_origin_of_coordinate_ne_zero p hp ha τ hτ (fermatPoint p v hv) 0 ?_,
    rootTwoCoordinate_not_regular p τ hp ha hτ v hv i j hij hi hj hz hs⟩
  simpa only [fermatPoint_X] using hz 0 (Ne.symm (Fin.succ_ne_zero i)) (Ne.symm (Fin.succ_ne_zero j))

end CanonicalRoots
