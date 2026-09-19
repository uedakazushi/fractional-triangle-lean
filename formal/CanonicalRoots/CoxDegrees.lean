import CanonicalRoots.CoxIdentities
import CanonicalRoots.Semantics

noncomputable section
namespace CanonicalRoots

/-- The presentation relations hold in the actual quotient group. -/
theorem degree_relation {n : ℕ} (p : Fin n → ℕ) (i : Fin n) :
    (p i : ℤ) • xDegree p i = cDegree p := by
  apply sub_eq_zero.mp
  change (p i : ℤ) • QuotientAddGroup.mk' (degreeRelations p) (Pi.single (some i) 1) -
    QuotientAddGroup.mk' (degreeRelations p) (Pi.single none 1) = 0
  rw [← map_zsmul, ← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact AddSubgroup.subset_closure (Set.mem_range_self i)

namespace Cox
/-- Integer certificates imply genuine group equalities, even in the presence of torsion. -/
theorem lattice_degree {G : Type*} [AddCommGroup G]
    (k : Kind) (a b c : ℤ) (xs : Fin 3 → G) (cc : G)
    (hrel : ∀ j, signature k a b c j • xs j = cc) (i : Fin 3) :
    defect k a b c • (∑ j, monomials k a b c i j • xs j) =
      weights k a b c i • (cc - ∑ j, xs j) := by
  calc
    _ = ∑ j, (defect k a b c * monomials k a b c i j) • xs j := by
      simp only [Finset.smul_sum, mul_smul]
    _ = ∑ j, (certificate k a b c i j • (signature k a b c j • xs j) -
        weights k a b c i • xs j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h := integral_degree k a b c i j
      have he : defect k a b c * monomials k a b c i j =
          certificate k a b c i j * signature k a b c j - weights k a b c i := by
        nlinarith [h]
      rw [he, sub_smul, mul_smul]
    _ = (∑ j, certificate k a b c i j) • cc - weights k a b c i • (∑ j, xs j) := by
      simp only [hrel, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum]
    _ = _ := by rw [certificate_row_sum, smul_sub]

end Cox
end CanonicalRoots
