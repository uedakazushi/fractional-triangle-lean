import CanonicalRoots.OutputRootWitness

noncomputable section
open CanonicalRoots

example : rootWitnessResidues 1 [2,3,7,43] = [1,2,6,42] := by decide +kernel
example : rootWitnessCoefficient 1 [2,3,7,43] = -3 := by decide +kernel
example : rootWitnessResidues 5 [2,3,7,47] = [1,1,4,28] := by decide +kernel
example : rootWitnessCoefficient 5 [2,3,7,47] = -2 := by decide +kernel

example {n a : ℕ} (t : Target n a) : rootWitnessDegree a t.signature = t.tau :=
  rootWitnessDegree_eq t.signature (fun i => lt_of_lt_of_le (by decide) (t.admissible.1 i))
    t.parameter_input t.tau t.root_equation

-- This equality is in the actual quotient degree group, without a torsion-free premise.
example {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    a • rootWitnessDegree a p = omegaDegree p := by
  rw [rootWitnessDegree_eq p hp ha τ hτ]
  exact hτ
