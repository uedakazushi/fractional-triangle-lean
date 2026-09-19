import CanonicalRoots.TwoCoordinatePoints
import CanonicalRoots.RootPointOrigin

noncomputable section
namespace CanonicalRoots.StabilizerTests

private theorem admissible6666 : AdmissibleSignature ![6,6,6,6] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

/-- The constructed stratum really maps away from the origin of the root quotient. -/
example : ∃ z : AmbientRing ![6,6,6,6] →ₐ[ℂ] ℂ,
    rootPoint ![6,6,6,6] (omegaDegree ![6,6,6,6]) z ≠
      rootOriginPoint ![6,6,6,6] (by decide +kernel) (omegaDegree ![6,6,6,6]) := by
  obtain ⟨z, _, _, hz⟩ := twoCoordinatePoint_exists ![6,6,6,6] (by decide +kernel)
    (by decide) 0 1 (by decide)
  exact ⟨z, rootPoint_ne_origin_of_coordinate_ne_zero _ admissible6666 (a := 1) (by decide) _
    (by simp [IsCanonicalRoot]) z 2 (hz 2 (by decide) (by decide))⟩

/-- An actual nonzero point with order-six stabilizer, for the u=2 canonical root. -/
example : ∃ z : AmbientRing ![6,6,6,6] →ₐ[ℂ] ℂ,
    z (ambientQuotient ![6,6,6,6] (MvPolynomial.X 2)) ≠ 0 ∧
    Nat.card (rootPointStabilizer ![6,6,6,6] (omegaDegree ![6,6,6,6]) z) = 6 := by
  obtain ⟨z, hi, hj, hz⟩ := twoCoordinatePoint_exists ![6,6,6,6] (by decide +kernel)
    (by decide) 0 1 (by decide)
  refine ⟨z, hz 2 (by decide) (by decide), ?_⟩
  exact twoCoordinateStabilizer_card _ admissible6666 (a := 1) (by decide) _
    (by simp [IsCanonicalRoot]) 0 1 2 (by decide) (by decide) (by decide) z hi hj hz

/-- The coordinate description accepts an inverse pair and reconstructs a quotient character. -/
example : ∃ χ : RootCharacter ![6,6,6,6] (omegaDegree ![6,6,6,6]),
    rootCharacterDegree _ _ χ (xDegree ![6,6,6,6] 0) = Additive.ofMul (-1 : ℂˣ) ∧
    rootCharacterDegree _ _ χ (xDegree ![6,6,6,6] 2) = 0 := by
  let χ := twoCoordinateCharacter ![6,6,6,6] admissible6666 (a := 1) (by decide)
    (omegaDegree ![6,6,6,6])
    (by simp [IsCanonicalRoot]) 0 1 (by decide) (-1) (by norm_num)
  have hspec (k : Fin 4) : rootCharacterDegree _ _ χ (xDegree ![6,6,6,6] k) =
      Additive.ofMul (twoCoordinateUnits 0 1 (-1) k) :=
    twoCoordinateCharacter_degree_x ![6,6,6,6] admissible6666 (a := 1) (by decide)
      (omegaDegree ![6,6,6,6]) (by simp [IsCanonicalRoot]) 0 1 (by decide) (-1) (by norm_num) k
  refine ⟨χ, ?_, ?_⟩
  · exact (hspec 0).trans (by simp)
  · exact (hspec 2).trans (by simp [twoCoordinateUnits])

/-- The triple (2,3,7,43) has trivial two-coordinate stabilizers, consistently with coprimality. -/
example (z : AmbientRing ![2,3,7,43] →ₐ[ℂ] ℂ)
    (hi : z (ambientQuotient ![2,3,7,43] (MvPolynomial.X 0)) = 0)
    (hj : z (ambientQuotient ![2,3,7,43] (MvPolynomial.X 1)) = 0)
    (hz : ∀ l, l ≠ 0 → l ≠ 1 → z (ambientQuotient ![2,3,7,43] (MvPolynomial.X l)) ≠ 0) :
    Nat.card (rootPointStabilizer ![2,3,7,43] (omegaDegree ![2,3,7,43]) z) = 1 := by
  apply twoCoordinateStabilizer_card _ _ (a := 1) (by decide) _
    (by simp [IsCanonicalRoot]) 0 1 2 (by decide) (by decide) (by decide) z hi hj hz
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

end CanonicalRoots.StabilizerTests
