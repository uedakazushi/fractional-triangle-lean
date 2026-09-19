import CanonicalRoots.PowerSeriesInvariantCotangent
import CanonicalRoots.CyclicPlaneInvariants
import CanonicalRoots.TwoCoordinateStabilizer

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (s : ℕ) (i j : Fin n)

def cyclicFormalWeights (ζ : rootsOfUnity s ℂ) (k : Fin n) : ℂ :=
  (twoCoordinateUnits i j ζ.val k : ℂ)

theorem cyclicFormalWeights_prod (hij : i ≠ j) (ζ : rootsOfUnity s ℂ) (d : Fin n →₀ ℕ) :
    d.prod (fun k a => cyclicFormalWeights s i j ζ k ^ a) =
      (ζ.val : ℂ) ^ d i * ((ζ.val⁻¹ : ℂˣ) : ℂ) ^ d j := by
  classical
  rw [Finsupp.prod_fintype _ _ (by simp)]
  rw [Finset.prod_eq_mul_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
  · simp only [cyclicFormalWeights, twoCoordinateUnits_left, twoCoordinateUnits_right i j hij]
  · intro k _ hk
    simp only [cyclicFormalWeights, twoCoordinateUnits_other i j _ k hk.1 hk.2, Units.val_one, one_pow]

/-- Arbitrarily many additional fixed variables do not change the cyclic congruence condition. -/
theorem cyclicFormalInvariantExponent_iff (hs : 0 < s) (hij : i ≠ j) (d : Fin n →₀ ℕ) :
    DiagonalInvariantExponent (cyclicFormalWeights s i j) d ↔ d i % s = d j % s := by
  let e : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![d i, d j]
  have h := cyclicMonomialValue_all_one_iff s hs e
  change (∀ ζ : rootsOfUnity s ℂ,
    ((ζ.val ^ d i * (ζ.val⁻¹) ^ d j : ℂˣ) : ℂ) = 1) ↔ d i % s = d j % s at h
  simpa only [DiagonalInvariantExponent, cyclicFormalWeights_prod s i j hij,
    Units.val_mul, Units.val_pow_eq_pow_val] using h

/-- The invariant monomial x_i^s cannot factor into two nonconstant invariant monomials. -/
theorem cyclicFormalIndecomposable_left (hs : 0 < s) (hij : i ≠ j) :
    DiagonalIndecomposableExponent (cyclicFormalWeights s i j) (Finsupp.single i s) := by
  classical
  refine ⟨by simp [ne_of_gt hs], (cyclicFormalInvariantExponent_iff s i j hs hij _).mpr ?_, ?_⟩
  · simp [Ne.symm hij]
  · intro e f hef he hf
    have hcoord (k : Fin n) : e k + f k = Finsupp.single i s k := congrArg (fun d => d k) hef
    have hout (k : Fin n) (hki : k ≠ i) : e k = 0 ∧ f k = 0 := by
      have h := hcoord k
      simp only [Finsupp.single_eq_of_ne hki] at h
      omega
    have hm : e i % s = 0 := by
      have h := (cyclicFormalInvariantExponent_iff s i j hs hij e).mp he
      rw [(hout j (Ne.symm hij)).1] at h
      simpa only [Nat.zero_mod] using h
    have hiSum : e i + f i = s := by simpa only [Finsupp.single_eq_same] using hcoord i
    by_cases hei : e i = 0
    · left
      ext k
      by_cases hki : k = i
      · subst k; exact hei
      · exact (hout k hki).1
    · right
      have hei' : e i = s := by
        by_contra hne
        have hlt : e i < s := by omega
        rw [Nat.mod_eq_of_lt hlt] at hm
        exact hei hm
      ext k
      by_cases hki : k = i
      · subst k; change f i = 0; omega
      · exact (hout k hki).2

/-- Swapping the two special variables preserves the exponent condition. -/
theorem cyclicFormalInvariantExponent_swap (hs : 0 < s) (hij : i ≠ j) (d : Fin n →₀ ℕ) :
    DiagonalInvariantExponent (cyclicFormalWeights s i j) d ↔
      DiagonalInvariantExponent (cyclicFormalWeights s j i) d := by
  rw [cyclicFormalInvariantExponent_iff s i j hs hij,
    cyclicFormalInvariantExponent_iff s j i hs (Ne.symm hij)]
  exact eq_comm

theorem cyclicFormalIndecomposable_right (hs : 0 < s) (hij : i ≠ j) :
    DiagonalIndecomposableExponent (cyclicFormalWeights s i j) (Finsupp.single j s) := by
  have h := cyclicFormalIndecomposable_left s j i hs (Ne.symm hij)
  exact ⟨h.1, (cyclicFormalInvariantExponent_swap s i j hs hij _).mpr h.2.1,
    fun e f hef he hf => h.2.2 e f hef
      ((cyclicFormalInvariantExponent_swap s i j hs hij _).mp he)
      ((cyclicFormalInvariantExponent_swap s i j hs hij _).mp hf)⟩

/-- The mixed invariant x_i*x_j remains indecomposable when the cyclic order is at least two. -/
theorem cyclicFormalIndecomposable_mixed (hs : 2 ≤ s) (hij : i ≠ j) :
    DiagonalIndecomposableExponent (cyclicFormalWeights s i j)
      (Finsupp.single i 1 + Finsupp.single j 1) := by
  classical
  have hs0 : 0 < s := by omega
  refine ⟨?_, (cyclicFormalInvariantExponent_iff s i j hs0 hij _).mpr ?_, ?_⟩
  · intro h
    have hc := congrArg (fun d : Fin n →₀ ℕ => d i) h
    simp [hij] at hc
  · simp [hij, Ne.symm hij]
  · intro e f hef he hf
    have hcoord (k : Fin n) : e k + f k = (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) k :=
      congrArg (fun d => d k) hef
    have hout (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) : e k = 0 ∧ f k = 0 := by
      have h := hcoord k
      simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hki, Finsupp.single_eq_of_ne hkj,
        zero_add] at h
      omega
    have hiSum : e i + f i = 1 := by simpa [hij] using hcoord i
    have hjSum : e j + f j = 1 := by simpa [Ne.symm hij] using hcoord j
    have heij : e i = e j := by
      have h := (cyclicFormalInvariantExponent_iff s i j hs0 hij e).mp he
      simpa only [Nat.mod_eq_of_lt (show e i < s by omega),
        Nat.mod_eq_of_lt (show e j < s by omega)] using h
    by_cases hei : e i = 0
    · left
      ext k
      by_cases hki : k = i
      · subst k; exact hei
      · by_cases hkj : k = j
        · subst k; change e j = 0; omega
        · exact (hout k hki hkj).1
    · right
      ext k
      by_cases hki : k = i
      · subst k; change f i = 0; omega
      · by_cases hkj : k = j
        · subst k; change f j = 0; omega
        · exact (hout k hki hkj).2

/-- Each additional fixed coordinate supplies its own indecomposable invariant monomial. -/
theorem cyclicFormalIndecomposable_extra (hs : 0 < s) (hij : i ≠ j)
    (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    DiagonalIndecomposableExponent (cyclicFormalWeights s i j) (Finsupp.single k 1) := by
  classical
  refine ⟨by simp, (cyclicFormalInvariantExponent_iff s i j hs hij _).mpr ?_, ?_⟩
  · simp [Ne.symm hki, Ne.symm hkj]
  · intro e f hef he hf
    have hcoord (l : Fin n) : e l + f l = Finsupp.single k 1 l := congrArg (fun d => d l) hef
    have hout (l : Fin n) (hlk : l ≠ k) : e l = 0 ∧ f l = 0 := by
      have h := hcoord l
      simp only [Finsupp.single_eq_of_ne hlk] at h
      omega
    have hkSum : e k + f k = 1 := by simpa only [Finsupp.single_eq_same] using hcoord k
    by_cases hek : e k = 0
    · left
      ext l
      by_cases hlk : l = k
      · subst l; exact hek
      · exact (hout l hlk).1
    · right
      ext l
      by_cases hlk : l = k
      · subst l; change f k = 0; omega
      · exact (hout l hlk).2

end CanonicalRoots
