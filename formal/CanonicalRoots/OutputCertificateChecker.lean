import CanonicalRoots.Final

namespace CanonicalRoots

/-- Exact whole-list checking: omissions, duplicates and altered equation data are rejected. -/
def checkEquationList (input : Input) (rows : List EquationData) : Bool :=
  decide (rows = enumerate input)

theorem checkEquationList_correct (input : Input) (rows : List EquationData) :
    checkEquationList input rows = true ↔ rows = enumerate input := by
  simp [checkEquationList]

/-- Check all decoded equation data against the whole enumeration, not only row validity.
Redundant display metadata has the normalization policy of decodeClassificationPayload. -/
def checkClassificationPayload (input : Input) (j : Lean.Json) : Bool :=
  decide (decodeClassificationPayload j = some (input.n,input.a,enumerate input))

theorem checkClassificationPayload_correct (input : Input) (j : Lean.Json) :
    checkClassificationPayload input j = true ↔
      decodeClassificationPayload j = some (input.n,input.a,enumerate input) := by
  simp [checkClassificationPayload]

theorem checkClassificationPayload_normal (input : Input) :
    checkClassificationPayload input (classificationPayload input) = true :=
  (checkClassificationPayload_correct input _).mpr (cli_payload_correct input)

end CanonicalRoots
