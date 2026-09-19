import CanonicalRoots.GradedWeightInvariance
import CanonicalRoots.HigherSemanticEnumeration

noncomputable section
namespace CanonicalRoots

theorem signature_permutation_of_productWeights {n a : ℕ} (p q : Fin n → ℕ)
    (hp : ∀ i, 0 < p i)
    (hdp : ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a)
    (hdq : ((∏ i, q i : ℕ) : ℤ) - ∑ i, (productWeights q i : ℤ) = a)
    (σ : Equiv.Perm (Fin n)) (hw : ∀ i, productWeights p i = productWeights q (σ i)) :
    ∀ i, p i = q (σ i) := by
  have hs : (∑ i, (productWeights p i : ℤ)) = ∑ i, (productWeights q i : ℤ) := by
    simp_rw [hw]
    exact Equiv.sum_comp σ (fun i => (productWeights q i : ℤ))
  have hP : (∏ i, p i) = ∏ i, q i := by
    have hPi : ((∏ i, p i : ℕ) : ℤ) = ((∏ i, q i : ℕ) : ℤ) := by omega
    exact_mod_cast hPi
  intro i
  apply mul_left_cancel₀ (ne_of_gt (productWeights_pos p hp i))
  rw [productWeights_mul, hw, productWeights_mul, hP]

/-- Sorted product-defect signatures at the same root index are recovered from
the actual graded algebra isomorphism of their Fermat models. -/
theorem higher_models_gradedEquiv_signature_eq {n a : ℕ} (p q : Fin n → ℕ)
    (hp : ∀ i, 2 ≤ p i) (hq : ∀ i, 2 ≤ q i) (hpm : StrictMono p) (hqm : StrictMono q)
    (hdp : ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a)
    (hdq : ((∏ i, q i : ℕ) : ℤ) - ∑ i, (productWeights q i : ℤ) = a)
    (e : GradedAlgEquiv (presentedPiece (fermat p) (productWeights p))
      (presentedPiece (fermat q) (productWeights q))) : p = q := by
  have hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp i)
  obtain ⟨σ, hσ⟩ := gradedEquiv_weights_permutation (fermat p) (fermat q)
    (fermat_no_constant_or_linear p hp) (fermat_no_constant_or_linear q hq)
    (productWeights p) (productWeights q) (productWeights_pos p hp0) e
  have he : p = q ∘ σ := funext (signature_permutation_of_productWeights p q hp0 hdp hdq σ hσ)
  have hm : Monotone (q ∘ σ) := by rw [← he]; exact hpm.monotone
  exact he.trans (Tuple.unique_monotone (τ := Equiv.refl _) hm hqm.monotone)

/-- Distinct signature rows returned by the higher enumerator give nonisomorphic
graded complex algebras, rather than merely different numerical keys. -/
theorem enumerateHigherCandidates_models_nonisomorphic {n a : ℕ} (ha : 1 ≤ a)
    (p q : Fin n → ℕ)
    (hp : List.ofFn p ∈ enumerateHigherCandidates n a)
    (hq : List.ofFn q ∈ enumerateHigherCandidates n a) (hpq : p ≠ q) :
    ¬Nonempty (GradedAlgEquiv (presentedPiece (fermat p) (productWeights p))
      (presentedPiece (fermat q) (productWeights q))) := by
  have hp2 : ∀ i, 2 ≤ p i := fun i =>
    ((enumerateHigherCandidates_iff n a ha _).mp hp).2.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hq2 : ∀ i, 2 ≤ q i := fun i =>
    ((enumerateHigherCandidates_iff n a ha _).mp hq).2.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  obtain ⟨_, hpm, _, hdp⟩ := (enumerateHigherCandidates_ofFn_iff p
    (fun i => lt_of_lt_of_le (by decide) (hp2 i)) ha).mp hp
  obtain ⟨_, hqm, _, hdq⟩ := (enumerateHigherCandidates_ofFn_iff q
    (fun i => lt_of_lt_of_le (by decide) (hq2 i)) ha).mp hq
  rintro ⟨e⟩
  exact hpq (higher_models_gradedEquiv_signature_eq p q hp2 hq2 hpm hqm hdp hdq e)

end CanonicalRoots
