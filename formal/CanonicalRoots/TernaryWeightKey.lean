import CanonicalRoots.RootSignatureEquivalence
import CanonicalRoots.GradedWeightInvariance
import CanonicalRoots.HypersurfaceNumerics

noncomputable section
namespace CanonicalRoots

theorem Target.hilbertSeries_eq_of_weights_permutation {n a : ℕ} (t s : Target (n + 1) a)
    (σ : Equiv.Perm (Fin (n + 1))) (hw : ∀ i, t.presentation.weights i = s.presentation.weights (σ i)) :
    rootHilbertSeries t.signature t.tau = rootHilbertSeries s.signature s.tau := by
  have hsum : (∑ i, t.presentation.weights i) = ∑ i, s.presentation.weights i := by
    simp_rw [hw]
    exact Equiv.sum_comp σ _
  have hh : t.presentation.relationDegree = s.presentation.relationDegree := by
    rw [t.relationDegree_eq_add_sum_weights, s.relationDegree_eq_add_sum_weights, hsum]
  let D : PowerSeries ℚ := ∏ i, (1 - PowerSeries.X ^ t.presentation.weights i)
  have hD : D = ∏ i, (1 - PowerSeries.X ^ s.presentation.weights i) := by
    dsimp [D]
    simp_rw [hw]
    exact Equiv.prod_comp σ (fun i => (1 - PowerSeries.X ^ s.presentation.weights i : PowerSeries ℚ))
  have hD0 : D ≠ 0 := by
    have hc : PowerSeries.constantCoeff D = 1 := by
      simp only [D, map_prod, map_sub, map_one, map_pow, PowerSeries.constantCoeff_X]
      apply Finset.prod_eq_one
      intro i hi
      rw [zero_pow (ne_of_gt (t.presentation.weights_pos i))]
      simp
    intro hz
    rw [hz, map_zero] at hc
    exact zero_ne_one hc
  apply mul_right_cancel₀ hD0
  calc
    _ = 1 - PowerSeries.X ^ t.presentation.relationDegree :=
      t.presentation.hilbertSeries_mul_denominator t.signature t.tau
    _ = rootHilbertSeries s.signature s.tau * D := by
      rw [hD, s.presentation.hilbertSeries_mul_denominator s.signature s.tau, hh]

/-- For actual ternary Targets at fixed a, the weight multiset is a complete
graded-isomorphism invariant. The proof does not assume an invertible polynomial model. -/
theorem Target.ternary_gradedEquiv_iff_weights {a : ℕ} (t s : Target 3 a) :
    Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau) (rootPiece s.signature s.tau)) ↔
      ∃ σ : Equiv.Perm (Fin 3), ∀ i, t.presentation.weights i = s.presentation.weights (σ i) := by
  constructor
  · rintro ⟨e⟩
    exact gradedEquiv_weights_permutation t.presentation.polynomial s.presentation.polynomial
      t.presentation.no_constant_or_linear s.presentation.no_constant_or_linear
      t.presentation.weights s.presentation.weights t.presentation.weights_pos
      (t.presentation.graded_equiv.trans (e.trans s.presentation.graded_equiv.symm))
  · rintro ⟨σ, hw⟩
    apply (ternary_root_gradedEquiv_iff_signature t.signature s.signature t.admissible s.admissible
      t.parameter_input t.tau s.tau t.root_equation s.root_equation).mpr
    apply ternary_root_hilbert_signature_eq t.signature s.signature t.admissible s.admissible
      t.parameter_input t.tau s.tau t.root_equation s.root_equation
    intro m
    have h := congrArg (PowerSeries.coeff m) (t.hilbertSeries_eq_of_weights_permutation s σ hw)
    simp only [rootHilbertSeries, PowerSeries.coeff_mk] at h
    exact_mod_cast h

end CanonicalRoots
