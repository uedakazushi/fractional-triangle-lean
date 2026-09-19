import CanonicalRoots.SignatureDivisorRecovery
import Mathlib.LinearAlgebra.Finsupp.LSum

noncomputable section
namespace CanonicalRoots

def multipleSumLinear (e : ℕ) : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ where
  toFun f := multipleSum f e
  map_add' f g := by
    apply Finsupp.sum_add_index
    · intro r; simp
    · intro r c d; split_ifs <;> simp
  map_smul' c f := by
    change (c • f).sum (fun r d => if e ∣ r then d else 0) =
      c * f.sum (fun r d => if e ∣ r then d else 0)
    rw [Finsupp.sum_smul_index (by intro r; simp)]
    simp only [Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> simp

theorem multipleSumLinear_apply (e : ℕ) (f : ℕ →₀ ℚ) :
    multipleSumLinear e f = multipleSum f e := rfl

theorem multipleSumLinear_single (e r : ℕ) (c : ℚ) :
    multipleSumLinear e (Finsupp.single r c) = if e ∣ r then c else 0 := by
  simp [multipleSumLinear, multipleSum]

/-- An atom retaining only nontrivial orders. Its coefficient is already divided
by the order, as in `signatureMultiplicity`. -/
def weightedOrderAtom (r : ℕ) (c : ℚ) : ℕ →₀ ℚ :=
  if 2 ≤ r then Finsupp.single r c else 0

theorem weightedOrderAtom_small (r s : ℕ) (c : ℚ) (hs : s < 2) :
    weightedOrderAtom r c s = 0 := by
  classical
  unfold weightedOrderAtom
  split_ifs with hr
  · exact Finsupp.single_eq_of_ne (by omega)
  · rfl

theorem multipleSumLinear_weightedOrderAtom (e r : ℕ) (c : ℚ)
    (he : 2 ≤ e) (hr : 0 < r) :
    multipleSumLinear e (weightedOrderAtom r c) = if e ∣ r then c else 0 := by
  classical
  by_cases hr2 : 2 ≤ r
  · simp [weightedOrderAtom, hr2, multipleSumLinear_single]
  · have hd : ¬ e ∣ r := by
      intro hd
      have := Nat.le_of_dvd hr hd
      omega
    simp [weightedOrderAtom, hr2, hd]

end CanonicalRoots
