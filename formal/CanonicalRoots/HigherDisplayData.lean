import CanonicalRoots.DisplayVariableOrder
import CanonicalRoots.HigherRealization

noncomputable section
namespace CanonicalRoots

def higherListWeight (ps : List ℕ) (j : ℕ) : ℤ :=
  (ps.map Int.ofNat).prod / ((ps.toArray[j]?.getD 1 : ℕ) : ℤ)

def higherCoordinateWeight {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : ℤ :=
  ((∏ j, p j : ℕ) : ℤ) / p i

def higherListOrder (ps : List ℕ) : List ℕ :=
  (List.range ps.length).mergeSort (fun i j => higherListWeight ps i ≤ higherListWeight ps j)

theorem map_finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp

theorem higherListWeight_ofFn {n : ℕ} (p : Fin n → ℕ) (i : Fin n) :
    higherListWeight (List.ofFn p) i.val = higherCoordinateWeight p i := by
  simp [higherListWeight, higherCoordinateWeight, List.map_ofFn, List.prod_ofFn, Nat.cast_prod]

theorem higherCoordinateWeight_eq_productWeights {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) :
    higherCoordinateWeight p = fun i => (productWeights p i : ℤ) :=
  funext (productWeights_div p hp)

theorem higherListOrder_ofFn {n : ℕ} (p : Fin n → ℕ) :
    higherListOrder (List.ofFn p) =
      (displayVariableOrder (higherCoordinateWeight p)).map Fin.val := by
  symm
  unfold displayVariableOrder higherListOrder
  have hh := List.map_mergeSort (f := (Fin.val : Fin n → ℕ))
    (l := List.finRange n) (r := fun i j => decide (higherCoordinateWeight p i ≤ higherCoordinateWeight p j))
    (s := fun i j => decide (higherListWeight (List.ofFn p) i ≤ higherListWeight (List.ofFn p) j))
    (by intro i hi j hj; rw [higherListWeight_ofFn, higherListWeight_ofFn])
  simpa only [map_finRange_val, List.length_ofFn] using hh

theorem higherEquation_weights_ofFn {n : ℕ} (a : ℕ) (p : Fin n → ℕ) :
    (higherEquation a (List.ofFn p)).weights = List.ofFn
      (fun i => higherCoordinateWeight p (displayVariablePermutation (higherCoordinateWeight p) i)) := by
  change (higherListOrder (List.ofFn p)).map (higherListWeight (List.ofFn p)) = _
  rw [higherListOrder_ofFn, List.map_map,
    List.ofFn_comp' (displayVariablePermutation (higherCoordinateWeight p)) (higherCoordinateWeight p),
    ofFn_displayVariablePermutation]
  apply List.map_congr_left
  intro i hi
  exact higherListWeight_ofFn p i

theorem higherEquation_exponents_ofFn {n : ℕ} (a : ℕ) (p : Fin n → ℕ) :
    (higherEquation a (List.ofFn p)).exponents = List.ofFn (fun i => List.ofFn
      (fun j => if i = displayVariablePermutation (higherCoordinateWeight p) j then (p i : ℤ) else 0)) := by
  change (List.range (List.ofFn p).length).map (fun i => (higherListOrder (List.ofFn p)).map
    (fun j => if i = j then (((List.ofFn p).toArray[i]?.getD 0 : ℕ) : ℤ) else 0)) = _
  rw [List.length_ofFn, ← map_finRange_val, List.map_map, higherListOrder_ofFn]
  conv_rhs => rw [List.ofFn_eq_map]
  apply List.map_congr_left
  intro i hi
  dsimp only [Function.comp_apply]
  rw [List.map_map, List.ofFn_comp' (displayVariablePermutation (higherCoordinateWeight p))
    (fun j => if i = j then (p i : ℤ) else 0), ofFn_displayVariablePermutation]
  apply List.map_congr_left
  intro j hj
  simp [Function.comp_apply, Fin.val_inj]

end CanonicalRoots
