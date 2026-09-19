import CanonicalRoots.RootMultiplicityFormula
import CanonicalRoots.RootDimension
import CanonicalRoots.RootDegreeQuotient

noncomputable section
namespace CanonicalRoots.BoxCountTests

private theorem admissible444 : AdmissibleSignature ![4,4,4] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

/-- Complex characters detect a nonzero torsion degree that rational degree cannot distinguish. -/
example : ∃ χ : RootCharacter ![4,4,4] (omegaDegree ![4,4,4]),
    χ (Multiplicative.ofAdd (rootDegreeQuotientMap ![4,4,4] (omegaDegree ![4,4,4])
      (xDegree ![4,4,4] 0 - xDegree ![4,4,4] 1))) ≠ 1 := by
  apply rootCharacters_separate ![4,4,4] admissible444 (a := 1) (by decide)
    (omegaDegree ![4,4,4]) (by simp [IsCanonicalRoot])
  intro hz
  have hl := (QuotientAddGroup.eq_zero_iff _).mp hz
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hl
  have hd := congrArg (rationalDegree ![4,4,4] (by decide)) hm
  norm_num [map_zsmul, map_sub, rationalDegree_omega, Fin.sum_univ_succ, zsmul_eq_mul] at hd
  have hm0 : m = 0 := hd
  subst m
  have he : xDegree ![4,4,4] 0 = xDegree ![4,4,4] 1 := sub_eq_zero.mp (by simpa using hm.symm)
  obtain ⟨t, _, ht⟩ := (degree_eq_iff ![4,4,4] _ _).mp he
  have hh := ht 0
  norm_num [Pi.single_apply] at hh
  omega

/-- The actual root box is counted with torsion retained in DegreeGroup. -/
example : Nat.card (RootBox ![4,4,4] (omegaDegree ![4,4,4]) 1) = 4 := by
  have h := canonicalRootBox_card ![4,4,4] admissible444 (a := 1) (by decide)
    (omegaDegree ![4,4,4]) (by simp [IsCanonicalRoot])
  simpa only [show signatureLcm ![4,4,4] = 4 from by decide +kernel,
    show canonicalRootScale ![4,4,4] 1 = 1 from by decide +kernel, pow_one, mul_one] using h

private theorem admissible23767 : AdmissibleSignature ![2,3,7,67] := by
  constructor
  · decide +kernel
  · norm_num [Fin.sum_univ_succ]

example : ringKrullDim (RootRing ![4,4,4] (omegaDegree ![4,4,4])) = 2 :=
  canonicalRoot_krullDim ![4,4,4] admissible444 (a := 1) (by decide)
    (omegaDegree ![4,4,4]) (by simp [IsCanonicalRoot])

/-- Dimension is proved for this actual root without assuming a hypersurface presentation. -/
example : ∃ τ : DegreeGroup ![2,3,7,67], IsCanonicalRoot ![2,3,7,67] 5 τ ∧
    ringKrullDim (RootRing ![2,3,7,67] τ) = 3 := by
  obtain ⟨τ, hτ⟩ := (canonicalRoot_exists_iff ![2,3,7,67] (by decide +kernel) (a := 5)).mpr
    (by decide +kernel)
  exact ⟨τ, hτ, canonicalRoot_krullDim ![2,3,7,67] admissible23767 (by decide) τ hτ⟩

/-- This scale is greater than one; no u=1 or pairwise-coprime realization shortcut is used. -/
example : Nat.card (RootBox ![2,3,7,67] (omegaDegree ![2,3,7,67]) 25) = 1758750 := by
  have h := canonicalRootBox_card ![2,3,7,67] admissible23767 (a := 1) (by decide)
    (omegaDegree ![2,3,7,67]) (by simp [IsCanonicalRoot])
  norm_num only [show signatureLcm ![2,3,7,67] = 2814 from by decide +kernel,
    show canonicalRootScale ![2,3,7,67] 1 = 25 from by decide +kernel] at h
  exact h

/-- A nonmaximal root is included: the root exists even though a hypersurface presentation is not assumed. -/
example : ∃ τ : DegreeGroup ![2,3,7,67], IsCanonicalRoot ![2,3,7,67] 5 τ ∧
    Nat.card (RootBox ![2,3,7,67] τ 5) = 70350 := by
  obtain ⟨τ, hτ⟩ := (canonicalRoot_exists_iff ![2,3,7,67] (by decide +kernel) (a := 5)).mpr
    (by decide +kernel)
  refine ⟨τ, hτ, ?_⟩
  have h := canonicalRootBox_card ![2,3,7,67] admissible23767 (a := 5) (by decide) τ hτ
  norm_num only [show signatureLcm ![2,3,7,67] = 2814 from by decide +kernel,
    show canonicalRootScale ![2,3,7,67] 5 = 5 from by decide +kernel] at h
  exact h

/-- Boundary cases of the finite fiber count include a single coordinate and negative carries. -/
example : Nat.card (BoundedSumFiber 1 3 (-5)) = 1 := boundedSumFiber_card 0 3 (by decide) (-5)
example : Nat.card (BoundedSumFiber 3 3 (-5)) = 9 := boundedSumFiber_card 2 3 (by decide) (-5)
example : Nat.card (BoundedSumFiber 4 1 8) = 1 := boundedSumFiber_card 3 1 (by decide) 8

example (P : RootHypersurfacePresentation ![4,4,4] (omegaDegree ![4,4,4])) :
    (P.relationDegree : ℚ) / ∏ i, (P.weights i : ℚ) = 1 / 4 := by
  have h := P.relationDegree_div_prod_weights_explicit ![4,4,4] admissible444
    (a := 1) (by decide) (omegaDegree ![4,4,4]) (by simp [IsCanonicalRoot])
  norm_num [Fin.sum_univ_succ] at h ⊢
  exact h

end CanonicalRoots.BoxCountTests

#check CanonicalRoots.rootBoxParametersEquiv
#check CanonicalRoots.rootBox_card
#check CanonicalRoots.canonicalRoot_finrank
#check CanonicalRoots.RootHypersurfacePresentation.relationDegree_div_prod_weights
#check CanonicalRoots.Target.numerical_identities
#check CanonicalRoots.canonicalRoot_krullDim
#check CanonicalRoots.Target.root_krullDim
#check CanonicalRoots.canonicalRootDegreeQuotient_finite
#check CanonicalRoots.canonicalRootCharacters_finite
#check CanonicalRoots.rootCharacters_trivial_iff
