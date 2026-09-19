import CanonicalRoots.BranchedAxisSupport

noncomputable section
namespace CanonicalRoots

/-- Degree of an axis monomial; a loop is a pure power. -/
def axisWeight (w : Fin 3 → ℕ) (i j : Fin 3) (k : ℕ) : ℕ :=
  if i = j then k * w i else k * w i + w j

theorem axisWeight_of_support {h : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (w : Fin 3 → ℕ) (hhom : MvPolynomial.IsWeightedHomogeneous w f h)
    (i j : Fin 3) (k : ℕ) (hc : f.coeff (axisSupportExponent i j k) ≠ 0) :
    axisWeight w i j k = h := by
  have he := hhom hc
  by_cases hij : i = j
  · simpa [axisSupportExponent, axisWeight, hij, Finsupp.weight_single, smul_eq_mul] using he
  · simpa [axisSupportExponent, axisWeight, hij, Finsupp.weight_single, smul_eq_mul] using he

theorem pure_weight_exponent {h : ℕ} (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (hdef : (∑ i, w i) < h) (i : Fin 3) (hd : w i ∣ h) :
    ∃ m : ℕ, 2 ≤ m ∧ m * w i = h := by
  obtain ⟨m, hm⟩ := hd
  have hle : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i)
  refine ⟨m, ?_, by simpa only [mul_comm] using hm.symm⟩
  have := hw i
  nlinarith

/-- A numerical pure power changes a branched graph to an invertible graph.
No assertion about the coefficient of that power in the original polynomial is made. -/
theorem numeric_branched_add_pure (w : Fin 3 → ℕ) (h : ℕ)
    (σ : Equiv.Perm (Fin 3)) (tag : Fin 7) (ht : 5 ≤ tag.val)
    (k : Fin 3 → ℕ) (hk : ∀ i, 2 ≤ k i)
    (hc : ∀ i, axisWeight w (σ i) (σ (threeAxisPattern tag i)) (k i) = h)
    (i : Fin 3) (hi : i ≠ 1) (m : ℕ) (hm : 2 ≤ m) (hpure : m * w (σ i) = h) :
    ∃ σ' : Equiv.Perm (Fin 3), ∃ t : Fin 5, ∃ k' : Fin 3 → ℕ,
      (∀ l, 2 ≤ k' l) ∧ ∀ l,
        axisWeight w (σ' l) (σ' (threeAxisPattern ⟨t.val, by omega⟩ l)) (k' l) = h := by
  classical
  obtain ⟨ρ, t, hρ⟩ := three_branched_add_loop_reduces tag ht i hi
  refine ⟨ρ.trans σ, t, (Function.update k i m) ∘ ρ, ?_, ?_⟩
  · intro l
    by_cases hl : ρ l = i
    · simpa [hl] using hm
    · simpa [hl] using hk (ρ l)
  · intro l
    change axisWeight w (σ (ρ l)) (σ (ρ (threeAxisPattern ⟨t.val, by omega⟩ l)))
      (Function.update k i m (ρ l)) = h
    rw [← hρ l]
    by_cases hl : ρ l = i
    · simpa [hl, axisWeight] using hpure
    · simpa [hl] using hc (ρ l)

end CanonicalRoots
