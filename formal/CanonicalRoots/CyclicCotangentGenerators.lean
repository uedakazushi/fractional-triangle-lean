import CanonicalRoots.CyclicInvariantExponents

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (s : ℕ) (i j : Fin n)

/-- The n+1 invariant cotangent monomials: the pure powers, the mixed monomial, and fixed coordinates. -/
def cyclicGeneratorExponent : Option (Fin n) → Fin n →₀ ℕ := by
  classical
  exact fun t => match t with
    | none => Finsupp.single i 1 + Finsupp.single j 1
    | some k => Finsupp.single k (if k = i ∨ k = j then s else 1)

theorem cyclicMixed_ne_single (hij : i ≠ j) (k : Fin n) (q : ℕ) :
    (Finsupp.single i 1 + Finsupp.single j 1 : Fin n →₀ ℕ) ≠ Finsupp.single k q := by
  classical
  intro h
  by_cases hki : k = i
  · subst k
    have he := congrArg (fun d : Fin n →₀ ℕ => d j) h
    simp [Ne.symm hij] at he
  · have he := congrArg (fun d : Fin n →₀ ℕ => d i) h
    simp [hij, Ne.symm hki] at he

theorem cyclicGeneratorExponent_injective (hs : 0 < s) (hij : i ≠ j) :
    Function.Injective (cyclicGeneratorExponent s i j) := by
  classical
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some l => exact (cyclicMixed_ne_single i j hij l _ hab).elim
  | some k =>
    cases b with
    | none => exact (cyclicMixed_ne_single i j hij k _ hab.symm).elim
    | some l =>
      congr 1
      by_contra hkl
      have he := congrArg (fun d : Fin n →₀ ℕ => d k) hab
      change (Finsupp.single k (if k = i ∨ k = j then s else 1) : Fin n →₀ ℕ) k =
        (Finsupp.single l (if l = i ∨ l = j then s else 1) : Fin n →₀ ℕ) k at he
      simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hkl] at he
      split_ifs at he
      omega

theorem cyclicGeneratorExponent_indecomposable (hs : 2 ≤ s) (hij : i ≠ j) (t : Option (Fin n)) :
    DiagonalIndecomposableExponent (cyclicFormalWeights s i j) (cyclicGeneratorExponent s i j t) := by
  classical
  cases t with
  | none => exact cyclicFormalIndecomposable_mixed s i j hs hij
  | some k =>
    by_cases hki : k = i
    · subst k
      simpa [cyclicGeneratorExponent] using cyclicFormalIndecomposable_left s i j (by omega) hij
    · by_cases hkj : k = j
      · subst k
        simpa [cyclicGeneratorExponent] using cyclicFormalIndecomposable_right s i j (by omega) hij
      · simpa [cyclicGeneratorExponent, hki, hkj] using
          cyclicFormalIndecomposable_extra s i j (by omega) hij k hki hkj

/-- The cyclic formal fixed ring has n+1 independent cotangent classes in n variables. -/
theorem cyclicFormalCotangent_independent (hs : 2 ≤ s) (hij : i ≠ j) :
    LinearIndependent ℂ (fun t : Option (Fin n) =>
      diagonalCotangentMonomial (cyclicFormalWeights s i j) (cyclicGeneratorExponent s i j t)
        (cyclicGeneratorExponent_indecomposable s i j hs hij t)) :=
  diagonalCotangentMonomials_linearIndependent _ _ (cyclicGeneratorExponent_indecomposable s i j hs hij)
    (cyclicGeneratorExponent_injective s i j (by omega) hij)

end CanonicalRoots
