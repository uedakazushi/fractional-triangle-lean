import CanonicalRoots.HigherDisplayData

noncomputable section
open CanonicalRoots

example : (higherEquation 1 [2,3,7,43]).weights = [42,258,602,903] ∧
    (higherEquation 1 [2,3,7,43]).exponents = [[0,0,0,2],[0,0,3,0],[0,7,0,0],[43,0,0,0]] := by
  norm_num [higherEquation, List.range_succ, List.mergeSort, List.merge]

example {n : ℕ} (a : ℕ) (p : Fin n → ℕ) :
    (higherEquation a (List.ofFn p)).exponents = List.ofFn (fun i => List.ofFn
      (fun j => if i = displayVariablePermutation (higherCoordinateWeight p) j then (p i : ℤ) else 0)) :=
  higherEquation_exponents_ofFn a p
