import CanonicalRoots.RootInvariants

noncomputable section
namespace CanonicalRoots.CharacterActionTests

private theorem admissible444 : AdmissibleSignature ![4,4,4] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

/-- Tests the fixed-ring theorem in a case with nontrivial degree torsion. -/
example : rootSubalgebra ![4,4,4] (omegaDegree ![4,4,4]) =
    ambientCharacterFixed ![4,4,4] (omegaDegree ![4,4,4]) :=
  rootSubalgebra_eq_characterFixed _ admissible444 (a := 1) (by decide) _
    (by simp [IsCanonicalRoot])

/-- Fixedness is equality of actual quotient elements, without a homogeneity premise on x. -/
example (x : AmbientRing ![4,4,4]) :
    x ∈ rootSubalgebra ![4,4,4] (omegaDegree ![4,4,4]) ↔
      ∀ χ : RootCharacter ![4,4,4] (omegaDegree ![4,4,4]),
        ambientCharacterAction _ _ χ x = x := by
  rw [rootSubalgebra_eq_characterFixed _ admissible444 (a := 1) (by decide) _
    (by simp [IsCanonicalRoot])]
  rfl

/-- A root outside the u=1 realization is covered without any hypersurface assumption. -/
example : ∃ τ : DegreeGroup ![2,3,7,67], IsCanonicalRoot ![2,3,7,67] 5 τ ∧
    rootSubalgebra ![2,3,7,67] τ = ambientCharacterFixed ![2,3,7,67] τ := by
  obtain ⟨τ, hτ⟩ := (canonicalRoot_exists_iff ![2,3,7,67] (by decide +kernel) (a := 5)).mpr
    (by decide +kernel)
  refine ⟨τ, hτ, rootSubalgebra_eq_characterFixed _ ?_ (by decide) τ hτ⟩
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

/-- Negative pieces really vanish; integer multiples were not silently replaced by naturals. -/
example : ambientPiece ![4,4,4] (-omegaDegree ![4,4,4]) = ⊥ := by
  apply ambientPiece_eq_bot_of_rationalDegree_neg _ (by decide +kernel)
  norm_num [map_neg, rationalDegree_omega, Fin.sum_univ_succ]

example {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (χ : RootCharacter p τ)
    (x : AmbientRing p) : ambientCharacterAction p τ χ⁻¹ (ambientCharacterAction p τ χ x) = x := by
  exact (ambientCharacterEquiv p τ χ).left_inv x

example {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (χ : RootCharacter p τ) (i : Fin n) :
    ambientCharacterAction p τ χ (ambientQuotient p (MvPolynomial.X i)) =
      rootCharacterValue p τ χ (xDegree p i) • ambientQuotient p (MvPolynomial.X i) :=
  ambientCharacterHom_X p τ χ i

end CanonicalRoots.CharacterActionTests
