import CanonicalRoots.CyclicInvariantLocal

noncomputable section
namespace CanonicalRoots.CyclicInvariantTests
open MvPolynomial

example : (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ∉ cyclicPlaneFixed 2 := by
  intro h
  have he := (mem_cyclicPlaneFixed_iff 2 (by decide) _).mp h (Finsupp.single 0 1)
    (by simp)
  norm_num [Finsupp.single_apply] at he

/-- The quotient coordinate order is W,U,V and must agree with xy,x^s,y^s. -/
example (s : ℕ) (hs : 0 < s) :
    (cyclicQuotientEquivFixed s hs (Ideal.Quotient.mkₐ ℂ _ (X 0)) : MvPolynomial (Fin 2) ℂ) =
      X 0 * X 1 := by
  rw [cyclicQuotientEquivFixed_coe, cyclicQuotientMap_mk]
  simp [cyclicPolynomialMap]

example (s : ℕ) (hs : 0 < s) :
    (cyclicQuotientEquivFixed s hs (Ideal.Quotient.mkₐ ℂ _ (X 1)) : MvPolynomial (Fin 2) ℂ) =
      X 0 ^ s := by
  rw [cyclicQuotientEquivFixed_coe, cyclicQuotientMap_mk]
  simp [cyclicPolynomialMap]

example (s : ℕ) (hs : 0 < s) :
    (cyclicQuotientEquivFixed s hs (Ideal.Quotient.mkₐ ℂ _ (X 2)) : MvPolynomial (Fin 2) ℂ) =
      X 1 ^ s := by
  rw [cyclicQuotientEquivFixed_coe, cyclicQuotientMap_mk]
  simp [cyclicPolynomialMap]

example : (X (0 : Fin 2) ^ 6 + X 0 * X 1 : MvPolynomial (Fin 2) ℂ) ∈ cyclicPlaneFixed 3 := by
  rw [← cyclicQuotientMap_range_eq_fixed 3 (by decide)]
  refine ⟨Ideal.Quotient.mkₐ ℂ _ (X 1 ^ 2 + X 0), ?_⟩
  change cyclicQuotientMap 3 (Ideal.Quotient.mkₐ ℂ _ (X 1 ^ 2 + X 0)) = _
  rw [cyclicQuotientMap_mk]
  simp [cyclicPolynomialMap, ← pow_mul]

example : ¬ IsRegularLocalRing (AugmentationLocalRing (cyclicPlaneOrigin 2)) :=
  cyclicPlaneFixed_origin_not_regular 2 (by decide)

example : ¬ IsRegularLocalRing (AugmentationLocalRing (cyclicPlaneOrigin 6)) :=
  cyclicPlaneFixed_origin_not_regular 6 (by decide)

end CanonicalRoots.CyclicInvariantTests

#check CanonicalRoots.cyclicQuotientEquivFixed
#check CanonicalRoots.cyclicInvariantOriginEquiv
#check CanonicalRoots.cyclicPlaneFixed_origin_not_regular
