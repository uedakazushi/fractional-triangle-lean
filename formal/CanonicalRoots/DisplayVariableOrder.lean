import CanonicalRoots.Payload
import Mathlib

noncomputable section
namespace CanonicalRoots

/-- Read a permutation from the actual ordered index list, retaining its tie-breaking order. -/
def permutationOfIndexList {n : ℕ} (l : List (Fin n)) (hl : l.Perm (List.finRange n)) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => l.get ⟨i.val,by have := hl.length_eq; simp at this; omega⟩) (by
    constructor
    · intro i j hij
      have hn : l.Nodup := hl.nodup_iff.mpr (List.nodup_finRange n)
      have hh := hn.injective_get hij
      exact Fin.ext (congrArg (fun z : Fin l.length => z.val) hh)
    · intro j
      have hj : j ∈ l := hl.mem_iff.mpr (List.mem_finRange j)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hj
      refine ⟨⟨i.val,by have := hl.length_eq; simp at this; omega⟩,?_⟩
      exact hi)

theorem ofFn_permutationOfIndexList {n : ℕ} (l : List (Fin n)) (hl : l.Perm (List.finRange n)) :
    List.ofFn (permutationOfIndexList l hl) = l := by
  apply List.ext_get
  · simpa using hl.length_eq.symm
  · intro i hi hj
    simp [permutationOfIndexList]
    rfl

def displayVariableOrder {n : ℕ} (w : Fin n → ℤ) : List (Fin n) :=
  (List.finRange n).mergeSort (fun i j => w i ≤ w j)

def displayVariablePermutation {n : ℕ} (w : Fin n → ℤ) : Equiv.Perm (Fin n) :=
  permutationOfIndexList (displayVariableOrder w) (List.mergeSort_perm _ _)

theorem ofFn_displayVariablePermutation {n : ℕ} (w : Fin n → ℤ) :
    List.ofFn (displayVariablePermutation w) = displayVariableOrder w :=
  ofFn_permutationOfIndexList _ _

theorem displayVariablePermutation_sorted {n : ℕ} (w : Fin n → ℤ) :
    Monotone (w ∘ displayVariablePermutation w) := by
  apply List.sortedLE_ofFn_iff.mp
  change (List.ofFn (fun i => w (displayVariablePermutation w i))).SortedLE
  rw [List.ofFn_comp' (displayVariablePermutation w) w, ofFn_displayVariablePermutation]
  exact (List.pairwise_map.mpr (List.pairwise_mergeSort'
    (fun i j => w i ≤ w j) (List.finRange n))).sortedLE

theorem ternaryEquation_weights (a : ℕ) (e : TernaryCandidate) :
    (ternaryEquation a e).weights = List.ofFn (candidateWeights e ∘ displayVariablePermutation (candidateWeights e)) := by
  change (ternaryEquation a e).weights = List.ofFn
    (fun i => candidateWeights e (displayVariablePermutation (candidateWeights e) i))
  rw [List.ofFn_comp' (displayVariablePermutation (candidateWeights e)) (candidateWeights e),
    ofFn_displayVariablePermutation]
  rfl

theorem ternaryEquation_exponents (a : ℕ) (e : TernaryCandidate) :
    (ternaryEquation a e).exponents = List.ofFn (fun i => List.ofFn
      (fun j => Cox.exponents e.kind e.alpha e.beta e.gamma i (displayVariablePermutation (candidateWeights e) j))) := by
  simp only [ternaryEquation]
  rw [List.ofFn_eq_map]
  apply List.map_congr_left
  intro i hi
  rw [List.ofFn_comp' (displayVariablePermutation (candidateWeights e))
    (Cox.exponents e.kind e.alpha e.beta e.gamma i), ofFn_displayVariablePermutation]
  rfl

end CanonicalRoots
