import CanonicalRoots.TernaryCoordinateSignature
import CanonicalRoots.WeightedSignatureMass
import CanonicalRoots.RootMultiplicityFormula

noncomputable section
namespace CanonicalRoots

theorem coordinateMultiplicity_mass (w : Fin 3 → ℕ) (h : ℕ) :
    orderMassLinear (coordinateMultiplicity w h) =
      (∑ i, if 2 ≤ w i then (w i : ℚ) * coordinateVertexCoefficient w h i else 0) +
        (1 / 2 : ℚ) * (∑ i, ∑ j, if i ≠ j ∧ 2 ≤ Nat.gcd (w i) (w j) then
          (Nat.gcd (w i) (w j) : ℚ) *
            ((h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j)
          else 0) := by
  classical
  simp only [coordinateMultiplicity, map_add, map_smul, map_sum, smul_eq_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    exact orderMassLinear_weightedOrderAtom _ _
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases heq : i = j <;> simp [heq, orderMassLinear_weightedOrderAtom]

namespace Target

theorem coordinateMultiplicity_nonneg {a : ℕ} (t : Target 3 a) (r : ℕ) :
    0 ≤ coordinateMultiplicity t.presentation.weights t.presentation.relationDegree r := by
  rw [t.coordinateMultiplicity_eq_signature]
  exact signatureMultiplicity_nonneg _ _

theorem coordinateMultiplicity_order_mul {a : ℕ} (t : Target 3 a) (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * coordinateMultiplicity t.presentation.weights t.presentation.relationDegree r =
      (List.ofFn t.signature : Multiset ℕ).count r := by
  rw [t.coordinateMultiplicity_eq_signature]
  exact signatureMultiplicity_order_mul _ _ hr

/-- The three-point condition follows from the actual ternary signature. -/
theorem coordinateMultiplicity_mass {a : ℕ} (t : Target 3 a) :
    orderMassLinear (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) = 3 := by
  rw [t.coordinateMultiplicity_eq_signature, signatureMultiplicity_mass]
  · simp
  · intro r hr
    have hl : r ∈ List.ofFn t.signature := by simpa only [Multiset.mem_coe] using hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    have := t.admissible.1 i
    omega

theorem coordinateMultiplicity_total {a : ℕ} (t : Target 3 a) :
    multipleSumLinear 1 (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) =
      ∑ i, (1 : ℚ) / t.signature i := by
  rw [t.coordinateMultiplicity_eq_signature, signatureMultiplicity_total_ofFn]

/-- The defect identity in finite coordinate data; no orbit classification is assumed. -/
theorem coordinateMultiplicity_defect {a : ℕ} (t : Target 3 a) :
    (a : ℚ) * ((t.presentation.relationDegree : ℚ) / ∏ i, (t.presentation.weights i : ℚ)) - 1 +
      multipleSumLinear 1 (coordinateMultiplicity t.presentation.weights t.presentation.relationDegree) = 0 := by
  rw [t.coordinateMultiplicity_total, t.relationDegree_div_prod_weights]
  norm_num only [show 3 - 2 = 1 from rfl, pow_one]
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (by have := t.parameter_input; omega : a ≠ 0)
  field_simp
  ring

end Target
end CanonicalRoots
