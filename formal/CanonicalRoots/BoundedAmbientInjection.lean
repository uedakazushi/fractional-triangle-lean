import CanonicalRoots.AmbientBasis

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- A nonzero polynomial of bounded first-variable degree stays nonzero in the Fermat quotient. -/
theorem ambientQuotient_ne_zero_of_degreeOf_lt {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : 0 < p 0) (f : MvPolynomial (Fin (n + 1)) ℂ) (hf : f ≠ 0)
    (hd : f.degreeOf 0 < p 0) : ambientQuotient p f ≠ 0 := by
  intro hz
  have hh := congrArg (ambientAdjoinEquiv p) hz
  rw [ambientAdjoinEquiv_quotient, map_zero] at hh
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (splitFermat_monic p hp)
    (by simpa using hf) (by simpa only [natDegree_finSuccEquiv, splitFermat_natDegree] using hd) hh

/-- Independence survives the actual quotient whenever all polynomials have bounded degree. -/
theorem ambientQuotient_linearIndependent_of_bounded {n : ℕ} {ι : Type*}
    (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (f : ι → MvPolynomial (Fin (n + 1)) ℂ) (hf : LinearIndependent ℂ f)
    (hd : ∀ i, (f i).degreeOf 0 < p 0) :
    LinearIndependent ℂ (fun i => ambientQuotient p (f i)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  have hsum : ∑ j ∈ s, c j • f j = 0 := by
    by_contra hn
    apply ambientQuotient_ne_zero_of_degreeOf_lt p hp _ hn
    · apply lt_of_le_of_lt (degreeOf_sum_le 0 s (fun j => c j • f j))
      apply (Finset.sup_lt_iff hp).mpr
      intro j hj
      rw [MvPolynomial.smul_eq_C_mul]
      exact lt_of_le_of_lt (degreeOf_C_mul_le _ _ _) (hd j)
    · simpa only [map_sum, map_smul] using hc
  exact (linearIndependent_iff'.mp hf) s c hsum i hi

end CanonicalRoots
