import CanonicalRoots.WeightedHypersurfacePieces
import CanonicalRoots.RootHilbertSeries

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def WeightedExponentIndex {n : ℕ} (w : Fin n → ℕ) (m : ℕ) :=
  {d : Fin n →₀ ℕ // Finsupp.weight w d = m}

def weightedPolynomialPieceBasis {n : ℕ} (w : Fin n → ℕ) (m : ℕ) :
    Module.Basis (WeightedExponentIndex w m) ℂ (weightedHomogeneousSubmodule ℂ w m) :=
  (basisRestrictSupport ℂ {d | Finsupp.weight w d = m}).map
    (LinearEquiv.ofEq _ _ (weightedHomogeneousSubmodule_eq_finsupp_supported ℂ w m).symm)

theorem weightedPolynomialPiece_finrank {n : ℕ} (w : Fin n → ℕ) (m : ℕ) :
    Module.finrank ℂ (weightedHomogeneousSubmodule ℂ w m) = Nat.card (WeightedExponentIndex w m) :=
  Module.finrank_eq_nat_card_basis (weightedPolynomialPieceBasis w m)

def weightedAntidiagonal {n : ℕ} (w : Fin n → ℕ) (m : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ m).filter (fun d => ∀ i, w i ∣ d i)

theorem mem_weightedAntidiagonal {n : ℕ} (w : Fin n → ℕ) (m : ℕ) (d : Fin n →₀ ℕ) :
    d ∈ weightedAntidiagonal w m ↔ (∑ i, d i) = m ∧ ∀ i, w i ∣ d i := by
  simp [weightedAntidiagonal, Finset.mem_finsuppAntidiag]

def weightedExponentEquivAntidiagonal {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (m : ℕ) :
    WeightedExponentIndex w m ≃ ↥(weightedAntidiagonal w m) where
  toFun d := ⟨Finsupp.equivFunOnFinite.symm (fun i => w i * d.val i), by
    apply (mem_weightedAntidiagonal w m _).mpr
    constructor
    · simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, Nat.mul_comm] using d.property
    · intro i
      exact dvd_mul_right (w i) (d.val i)⟩
  invFun d := ⟨Finsupp.equivFunOnFinite.symm (fun i => d.val i / w i), by
    have hd := (mem_weightedAntidiagonal w m d.val).mp d.property
    rw [Finsupp.weight_eq_sum]
    simpa [nsmul_eq_mul, Nat.div_mul_cancel (hd.2 _)] using hd.1⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    simp [Nat.mul_div_cancel_left _ (hw i)]
  right_inv d := by
    apply Subtype.ext
    ext i
    have hd := ((mem_weightedAntidiagonal w m d.val).mp d.property).2 i
    simp [Nat.mul_div_cancel' hd]

def weightedPolynomialHilbertSeries {n : ℕ} (w : Fin n → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun m => (Module.finrank ℂ (weightedHomogeneousSubmodule ℂ w m) : ℚ))

def weightedGeometricSeries {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) : PowerSeries ℚ :=
  ∏ i, PowerSeries.expand (w i) (ne_of_gt (hw i)) (PowerSeries.invOneSubPow ℚ 1).val

theorem weightedGeometricSeries_coeff {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (m : ℕ) :
    PowerSeries.coeff m (weightedGeometricSeries w hw) = (weightedAntidiagonal w m).card := by
  classical
  rw [weightedGeometricSeries, PowerSeries.coeff_prod]
  have hc (d : Fin n →₀ ℕ) :
      (∏ i, PowerSeries.coeff (d i)
        (PowerSeries.expand (w i) (ne_of_gt (hw i)) (PowerSeries.invOneSubPow ℚ 1).val)) =
        if ∀ i, w i ∣ d i then (1 : ℚ) else 0 := by
    simp only [PowerSeries.coeff_expand, PowerSeries.invOneSubPow,
      PowerSeries.coeff_mk, Nat.zero_add, Nat.choose_zero_right, Nat.cast_one]
    by_cases hd : ∀ i, w i ∣ d i
    · simp [hd]
    · rw [ite_eq_right hd]
      obtain ⟨i, hi⟩ := not_forall.mp hd
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simp_rw [hc]
  exact Finset.sum_boole _ _

/-- The product of geometric series counts the basis of the actual polynomial component. -/
theorem weightedPolynomialHilbertSeries_eq_geometric {n : ℕ}
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    weightedPolynomialHilbertSeries w = weightedGeometricSeries w hw := by
  apply PowerSeries.ext
  intro m
  rw [weightedPolynomialHilbertSeries, PowerSeries.coeff_mk, weightedPolynomialPiece_finrank,
    Nat.card_congr (weightedExponentEquivAntidiagonal w hw m), Nat.card_eq_fintype_card,
    Fintype.card_coe, weightedGeometricSeries_coeff]

theorem weightedPolynomialHilbertSeries_mul_denominator {n : ℕ}
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    weightedPolynomialHilbertSeries w * ∏ i, (1 - PowerSeries.X ^ w i) = 1 := by
  rw [weightedPolynomialHilbertSeries_eq_geometric w hw, weightedGeometricSeries,
    ← Finset.prod_mul_distrib]
  have h (i : Fin n) :
      PowerSeries.expand (w i) (ne_of_gt (hw i)) (PowerSeries.invOneSubPow ℚ 1).val *
        (1 - PowerSeries.X ^ w i) = 1 := by
    have he := congrArg (PowerSeries.expand (w i) (ne_of_gt (hw i)))
      (PowerSeries.invOneSubPow ℚ 1).val_inv
    simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one,
      map_mul, map_sub, map_one, PowerSeries.expand_X] using he
  simp_rw [h]
  simp

end CanonicalRoots
