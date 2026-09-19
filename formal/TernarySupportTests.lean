import CanonicalRoots.TargetTernarySupport

noncomputable section
open CanonicalRoots MvPolynomial

-- The seventh pattern is genuinely needed before adding the positive link.
example : ∀ r : Fin 6, ∀ t : Fin 5, ¬ ∀ i : Fin 3,
    threeAxisPattern 6 (threeCoordinatePermutation r i) =
      threeCoordinatePermutation r (threeAxisPattern ⟨t.val, Nat.lt_trans t.isLt (by decide)⟩ i) := by
  decide +kernel

-- An additional pure power changes either branched graph to an invertible graph.
example : ∃ ρ : Equiv.Perm (Fin 3), ∃ t : Fin 5, ∀ l,
    (Function.update (threeAxisPattern 6) 2 2) (ρ l) =
      ρ (threeAxisPattern ⟨t.val, by omega⟩ l) :=
  three_branched_add_loop_reduces 6 (by decide) 2 (by decide)

-- Positive defect and the seven axis terms alone do not imply isolatedness.
example : ¬ IsolatedAtOrigin
    ((X 1 : MvPolynomial (Fin 3) ℂ) * (X 0 ^ 4 + X 1 ^ 4 + X 2 ^ 4)) := by
  intro hf
  have hlin : HasNoConstantOrLinear
      ((X 1 : MvPolynomial (Fin 3) ℂ) * (X 0 ^ 4 + X 1 ^ 4 + X 2 ^ 4)) := by
    constructor
    · simp [coeff_X_mul', Finsupp.mem_support_iff]
    · intro i
      fin_cases i <;> norm_num [coeff_X_mul', Finsupp.mem_support_iff, coeff_X_pow]
  have hX (i : Fin 3) : IsWeightedHomogeneous (fun _ : Fin 3 => (1 : ℕ)) (X i : MvPolynomial (Fin 3) ℂ) 1 :=
    isWeightedHomogeneous_X ℂ _ i
  have hhom : IsWeightedHomogeneous (fun _ : Fin 3 => (1 : ℕ))
      ((X 1 : MvPolynomial (Fin 3) ℂ) * (X 0 ^ 4 + X 1 ^ 4 + X 2 ^ 4)) 5 := by
    convert (hX 1).mul (((hX 0).pow 4).add ((hX 1).pow 4) |>.add ((hX 2).pow 4)) using 1
  exact isolated_ternary_not_X_dvd _ hf hlin (fun _ => 1) (by decide) hhom 1
    (dvd_mul_right _ _)

-- The coprimality conditions apply to actual Targets, before any family selection.
example {a : ℕ} (t : Target 3 a) :
    Nat.Coprime a (Nat.gcd (t.presentation.weights 0) (t.presentation.weights 2)) :=
  t.ternary_coprime_parameter_pair 0 2 (by decide)

example {a : ℕ} (t : Target 3 a)
    (h : ¬ t.presentation.weights 1 ∣ t.presentation.relationDegree) :
    Nat.Coprime a (t.presentation.weights 1) :=
  t.ternary_coprime_parameter_vertex 1 h

end
