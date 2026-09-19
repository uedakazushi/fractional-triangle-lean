import CanonicalRoots.DivisorSumLinear
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.GCD.Basic

noncomputable section
namespace CanonicalRoots

def coordinateVertexCoefficient (w : Fin 3 → ℕ) (h : ℕ) (i : Fin 3) : ℚ :=
  if w i ∣ h then 0 else (w i : ℚ)⁻¹

/-- A finite rational coefficient vector derived from the weights. It is not
declared to be a multiset of orbit orders. Equality with actual signature
multiplicities must be proved separately. -/
def coordinateMultiplicity (w : Fin 3 → ℕ) (h : ℕ) : ℕ →₀ ℚ :=
  (∑ i, weightedOrderAtom (w i) (coordinateVertexCoefficient w h i)) +
    (1 / 2 : ℚ) • (∑ i, ∑ j, if i = j then 0 else
      weightedOrderAtom (Nat.gcd (w i) (w j))
        ((h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j))

theorem coordinateMultiplicity_small (w : Fin 3 → ℕ) (h s : ℕ) (hs : s < 2) :
    coordinateMultiplicity w h s = 0 := by
  have hz (r : ℕ) (c : ℚ) : weightedOrderAtom r c s = 0 := weightedOrderAtom_small r s c hs
  simp [coordinateMultiplicity, Finset.sum_apply, apply_ite, ite_apply, hz]

theorem coordinateMultiplicity_profile (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (h e : ℕ) (he : 2 ≤ e) :
    multipleSumLinear e (coordinateMultiplicity w h) =
      (∑ i, if e ∣ w i then coordinateVertexCoefficient w h i else 0) +
        (1 / 2 : ℚ) * (∑ i, ∑ j, if i ≠ j ∧ e ∣ w i ∧ e ∣ w j then
          (h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j
          else 0) := by
  classical
  have hi (i : Fin 3) := multipleSumLinear_weightedOrderAtom e (w i)
    (coordinateVertexCoefficient w h i) he (hw i)
  have hij (i j : Fin 3) : multipleSumLinear e (if i = j then 0 else
      weightedOrderAtom (Nat.gcd (w i) (w j))
        ((h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j)) =
      if i ≠ j ∧ e ∣ w i ∧ e ∣ w j then
        (h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j
        else 0 := by
    by_cases heq : i = j
    · simp [heq]
    · simp only [heq, ↓reduceIte, not_false_eq_true, true_and]
      rw [multipleSumLinear_weightedOrderAtom e _ _ he (Nat.gcd_pos_of_pos_left _ (hw i))]
      simp [Nat.dvd_gcd_iff, heq]
  simp only [coordinateMultiplicity, map_add, map_smul, map_sum, hi, hij, smul_eq_mul]

theorem coordinateMultiplicity_reindex (w : Fin 3 → ℕ) (h : ℕ) (σ : Equiv.Perm (Fin 3)) :
    coordinateMultiplicity (w ∘ σ) h = coordinateMultiplicity w h := by
  classical
  unfold coordinateMultiplicity
  congr 1
  · exact Equiv.sum_comp σ (fun i => weightedOrderAtom (w i) (coordinateVertexCoefficient w h i))
  · congr 1
    let F (i j : Fin 3) : ℕ →₀ ℚ := if i = j then 0 else
      weightedOrderAtom (Nat.gcd (w i) (w j))
        ((h : ℚ) / ((w i : ℚ) * w j) - coordinateVertexCoefficient w h i - coordinateVertexCoefficient w h j)
    have hd : (∑ i, ∑ j, F (σ i) (σ j)) = ∑ i, ∑ j, F i j := by
      calc
        _ = ∑ i, ∑ j, F (σ i) j := Finset.sum_congr rfl (fun i _ => Equiv.sum_comp σ (F (σ i)))
        _ = _ := Equiv.sum_comp σ (fun i => ∑ j, F i j)
    simpa only [F, σ.injective.eq_iff, coordinateVertexCoefficient, Function.comp_apply] using hd

theorem coordinateMultiplicity_profile_none (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (h e : ℕ) (he : 2 ≤ e) (hd : ∀ i, ¬ e ∣ w i) :
    multipleSumLinear e (coordinateMultiplicity w h) = 0 := by
  simp [coordinateMultiplicity_profile w hw h e he, hd]

theorem coordinateMultiplicity_profile_single (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (h e : ℕ) (he : 2 ≤ e) (h0 : e ∣ w 0) (h1 : ¬ e ∣ w 1) (h2 : ¬ e ∣ w 2) :
    multipleSumLinear e (coordinateMultiplicity w h) = coordinateVertexCoefficient w h 0 := by
  simp [coordinateMultiplicity_profile w hw h e he, Fin.sum_univ_succ, h0, h1, h2]

theorem coordinateMultiplicity_profile_pair (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (h e : ℕ) (he : 2 ≤ e) (h0 : e ∣ w 0) (h1 : e ∣ w 1) (h2 : ¬ e ∣ w 2) :
    multipleSumLinear e (coordinateMultiplicity w h) = (h : ℚ) / ((w 0 : ℚ) * w 1) := by
  simp only [coordinateMultiplicity_profile w hw h e he, Fin.sum_univ_three]
  norm_num [h0, h1, h2, mul_comm (w 1 : ℚ) (w 0 : ℚ)]
  ring

end CanonicalRoots
