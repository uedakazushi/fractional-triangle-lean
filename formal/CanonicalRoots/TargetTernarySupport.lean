import CanonicalRoots.BranchedAxisSupport
import CanonicalRoots.TernaryPoleArithmetic

noncomputable section
namespace CanonicalRoots.Target

theorem ternary_pair_weight_gcd_dvd {a : ℕ} (t : Target 3 a)
    (i j : Fin 3) (hij : i ≠ j) :
    Nat.gcd (t.presentation.weights i) (t.presentation.weights j) ∣ t.presentation.relationDegree :=
  isolated_ternary_pair_gcd_dvd t.presentation.polynomial t.presentation.isolated
    t.presentation.no_constant_or_linear t.presentation.weights t.presentation.weights_pos
    t.presentation.homogeneous i j hij

theorem ternary_coprime_parameter_pair {a : ℕ} (t : Target 3 a)
    (i j : Fin 3) (hij : i ≠ j) :
    Nat.Coprime a (Nat.gcd (t.presentation.weights i) (t.presentation.weights j)) :=
  ternary_pair_gcd_coprime_defect t.presentation.weights t.weights_gcd_eq_one
    t.relationDegree_eq_add_sum_weights t.ternary_pair_weight_gcd_dvd i j hij

theorem ternary_coprime_parameter_vertex {a : ℕ} (t : Target 3 a)
    (i : Fin 3) (hi : ¬ t.presentation.weights i ∣ t.presentation.relationDegree) :
    Nat.Coprime a (t.presentation.weights i) :=
  isolated_ternary_vertex_coprime_defect t.presentation.polynomial t.presentation.isolated
    t.presentation.no_constant_or_linear t.presentation.weights t.presentation.weights_pos
    t.presentation.homogeneous t.weights_gcd_eq_one t.relationDegree_eq_add_sum_weights i hi

/-- The actual Target presentation admits an invertible support or a branched
support with a positive link. No classification assumption is used. -/
theorem ternary_five_or_branched_link {a : ℕ} (t : Target 3 a) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ tag : Fin 7, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧
      (∀ i, t.presentation.polynomial.coeff
        (axisSupportExponent (σ i) (σ (threeAxisPattern tag i)) (k i)) ≠ 0) ∧
      (tag.val < 5 ∨ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        t.presentation.polynomial.coeff
          (Finsupp.single (σ 0) m + Finsupp.single (σ 2) n) ≠ 0) := by
  apply isolated_ternary_five_or_branched_link t.presentation.polynomial t.presentation.isolated
    t.presentation.no_constant_or_linear t.presentation.weights t.presentation.weights_pos
    t.presentation.homogeneous
  have := t.relationDegree_eq_add_sum_weights
  have := t.parameter_input
  omega

end CanonicalRoots.Target
