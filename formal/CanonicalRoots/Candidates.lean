import CanonicalRoots.ExponentBound
import CanonicalRoots.CandidateData

namespace CanonicalRoots
open Cox

@[simp] theorem mem_kinds (k : Kind) : k ∈ kinds := by cases k <;> simp [kinds]

theorem mem_ternaryBox (a : ℕ) (e : TernaryCandidate) :
    e ∈ ternaryBox a ↔ e.alpha ≤ a+6 ∧ e.beta ≤ a+6 ∧ e.gamma ≤ a+6 := by
  cases e with
  | mk k x y z => simp [ternaryBox, List.mem_flatMap, List.mem_map, List.mem_range,
      TernaryCandidate.mk.injEq, show a+7 = (a+6)+1 by omega]

/-- All-input arithmetic completeness of the baseline box, before key deduplication. -/
theorem enumerateTernaryCandidates_iff (a : ℕ) (ha : 1 ≤ a) (e : TernaryCandidate) :
    e ∈ enumerateTernaryCandidates a ↔ ArithmeticTernary a e := by
  simp only [enumerateTernaryCandidates, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro he
    have hb := exponent_bound e.kind e.alpha e.beta e.gamma a
      (by exact_mod_cast he.1) (by exact_mod_cast he.2.1)
      (by exact_mod_cast he.2.2.1) (by exact_mod_cast ha) he.2.2.2.2
    exact ⟨(mem_ternaryBox a e).mpr (by exact_mod_cast hb), he⟩


end CanonicalRoots
