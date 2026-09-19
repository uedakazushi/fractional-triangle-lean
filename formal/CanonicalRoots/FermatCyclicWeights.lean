import CanonicalRoots.RootFormalCotangent
import CanonicalRoots.CyclicInvariantExponents

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
  (v : Fin (n + 1) → ℂ) (hv : ∑ l, v l ^ p l = 0)
  (i j : Fin n) (hij : i ≠ j) (hi : v i.succ = 0) (hj : v j.succ = 0)
  (hz : ∀ l, l ≠ i.succ → l ≠ j.succ → v l ≠ 0)

def fermatTwoCoordinateStabilizerEquiv :
    rootPointStabilizer p τ (fermatPoint p v hv) ≃*
      rootsOfUnity (Nat.gcd (p i.succ) (p j.succ)) ℂ :=
  twoCoordinateStabilizerEquiv p hp ha τ hτ i.succ j.succ 0
    (by simpa using hij) (Ne.symm (Fin.succ_ne_zero i)) (Ne.symm (Fin.succ_ne_zero j)) (fermatPoint p v hv)
    (by simpa only [fermatPoint_X] using hi) (by simpa only [fermatPoint_X] using hj)
    (by simpa only [fermatPoint_X] using hz)

/-- Every original stabilizer eigenvalue in the formal chart has the explicit cyclic shape. -/
theorem fermatTailWeights_eq_cyclic (χ : rootPointStabilizer p τ (fermatPoint p v hv)) (k : Fin n) :
    fermatTailWeights p τ v hv χ k =
      cyclicFormalWeights (Nat.gcd (p i.succ) (p j.succ)) i j
        (fermatTwoCoordinateStabilizerEquiv p τ hp ha hτ v hv i j hij hi hj hz χ) k := by
  have hs := twoCoordinateStabilizer_shape p hp ha τ hτ i.succ j.succ 0
    (by simpa using hij) (Ne.symm (Fin.succ_ne_zero i)) (Ne.symm (Fin.succ_ne_zero j)) (fermatPoint p v hv)
    (by simpa only [fermatPoint_X] using hz) χ.val χ.property
  change ((rootCharacterDegree p τ χ.val (xDegree p k.succ)).toMul : ℂ) =
    (twoCoordinateUnits i j (rootCharacterDegree p τ χ.val (xDegree p i.succ)).toMul k : ℂ)
  by_cases hki : k = i
  · subst k
    rw [twoCoordinateUnits_left]
  · by_cases hkj : k = j
    · subst k
      rw [twoCoordinateUnits_right i j hij]
      exact congrArg (fun u : Additive ℂˣ => (u.toMul : ℂ)) hs.2.1
    · rw [twoCoordinateUnits_other i j _ k hki hkj]
      exact congrArg (fun u : Additive ℂˣ => (u.toMul : ℂ))
        (hs.2.2.2 k.succ (by simpa using hki) (by simpa using hkj))

include hp ha hτ hij hi hj hz in
/-- The actual stabilizer and the cyclic group have exactly the same invariant formal monomials. -/
theorem fermatInvariantExponent_iff_cyclic (d : Fin n →₀ ℕ) :
    DiagonalInvariantExponent (fermatTailWeights p τ v hv) d ↔
      DiagonalInvariantExponent (cyclicFormalWeights (Nat.gcd (p i.succ) (p j.succ)) i j) d := by
  let e := fermatTwoCoordinateStabilizerEquiv p τ hp ha hτ v hv i j hij hi hj hz
  have he (χ : rootPointStabilizer p τ (fermatPoint p v hv)) :
      fermatTailWeights p τ v hv χ = cyclicFormalWeights (Nat.gcd (p i.succ) (p j.succ)) i j (e χ) :=
    funext (fermatTailWeights_eq_cyclic p τ hp ha hτ v hv i j hij hi hj hz χ)
  constructor
  · intro h ζ
    obtain ⟨χ, rfl⟩ := e.surjective ζ
    rw [← he χ]
    exact h χ
  · intro h χ
    rw [he χ]
    exact h (e χ)

include hp ha hτ hij hi hj hz in
theorem fermatIndecomposableExponent_iff_cyclic (d : Fin n →₀ ℕ) :
    DiagonalIndecomposableExponent (fermatTailWeights p τ v hv) d ↔
      DiagonalIndecomposableExponent (cyclicFormalWeights (Nat.gcd (p i.succ) (p j.succ)) i j) d := by
  unfold DiagonalIndecomposableExponent
  simp only [fermatInvariantExponent_iff_cyclic p τ hp ha hτ v hv i j hij hi hj hz]

end CanonicalRoots
