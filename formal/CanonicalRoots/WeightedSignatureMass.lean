import CanonicalRoots.DivisorSumLinear
import CanonicalRoots.RootPeriodSignatureProfile

noncomputable section
namespace CanonicalRoots

/-- The number of entries represented by a count/order coefficient vector. -/
def orderMassLinear : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ where
  toFun f := f.sum fun r c => (r : ℚ) * c
  map_add' f g := by
    change (f + g).sum (fun r c => (r : ℚ) * c) =
      f.sum (fun r c => (r : ℚ) * c) + g.sum (fun r c => (r : ℚ) * c)
    apply Finsupp.sum_add_index
    · intro r; simp
    · intro r c d; simp [mul_add]
  map_smul' c f := by
    change (c • f).sum (fun r d => (r : ℚ) * d) =
      c * f.sum (fun r d => (r : ℚ) * d)
    rw [Finsupp.sum_smul_index (by intro r; simp)]
    simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    ring

theorem orderMassLinear_single (r : ℕ) (c : ℚ) :
    orderMassLinear (Finsupp.single r c) = (r : ℚ) * c := by
  simp [orderMassLinear]

theorem orderMassLinear_weightedOrderAtom (r : ℕ) (c : ℚ) :
    orderMassLinear (weightedOrderAtom r c) = if 2 ≤ r then (r : ℚ) * c else 0 := by
  classical
  by_cases hr : 2 ≤ r <;> simp [weightedOrderAtom, hr, orderMassLinear_single]

theorem signatureMultiplicity_nonneg (s : Multiset ℕ) (r : ℕ) :
    0 ≤ signatureMultiplicity s r := by
  rw [signatureMultiplicity_apply]
  positivity

theorem signatureMultiplicity_order_mul (s : Multiset ℕ) (r : ℕ) (hr : 0 < r) :
    (r : ℚ) * signatureMultiplicity s r = s.count r := by
  rw [signatureMultiplicity_apply]
  exact mul_div_cancel₀ _ (by exact_mod_cast ne_of_gt hr)

theorem signatureMultiplicity_mass (s : Multiset ℕ) (hs : ∀ r ∈ s, 0 < r) :
    orderMassLinear (signatureMultiplicity s) = s.card := by
  classical
  change (signatureMultiplicity s).sum (fun r c => (r : ℚ) * c) = _
  unfold signatureMultiplicity
  rw [Finsupp.onFinset_sum _ (fun _ => by simp)]
  have he : (∑ r ∈ s.toFinset, (r : ℚ) * ((s.count r : ℚ) / r)) =
      ∑ r ∈ s.toFinset, (s.count r : ℚ) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact mul_div_cancel₀ _ (by exact_mod_cast ne_of_gt (hs r (Multiset.mem_toFinset.mp hr)))
  rw [he]
  exact_mod_cast Multiset.toFinset_sum_count_eq s

theorem signatureMultiplicity_total_ofFn {n : ℕ} (p : Fin n → ℕ) :
    multipleSumLinear 1 (signatureMultiplicity (List.ofFn p : Multiset ℕ)) =
      ∑ i, (1 : ℚ) / p i := by
  change signatureDivisorProfile (List.ofFn p : Multiset ℕ) 1 = _
  simp [signatureDivisorProfile_ofFn]

end CanonicalRoots
