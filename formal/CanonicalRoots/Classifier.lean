import CanonicalRoots.EquationJsonCodec

namespace CanonicalRoots
open Lean

structure Input where
  n : ℕ
  a : ℕ
  dimension_input : 3 ≤ n
  parameter_input : 1 ≤ a

/-- The public total classifier; its semantic contract is proved in Final.lean. -/
def enumerate (input : Input) : List EquationData := enumerateCandidateEquations input.n input.a

/-- Pure successful payload encoder. The executable is connected only after final verification. -/
def encodeClassificationPayload (n a : ℕ) (rows : List EquationData) : Json :=
  Json.mkObj [("schema",.str "canonical-root-equations-v1"),
    ("status",.str "ok"), ("verification_status",.str "FULL_CLASSIFICATION_VERIFIED"),
    ("integer_encoding",.str "decimal strings"),
    ("input",Json.mkObj [("n",jsonNat n),("a",jsonNat a)]),
    ("count",jsonNat rows.length), ("equations",.arr (rows.map equationJson).toArray)]

def classificationPayload (input : Input) : Json :=
  encodeClassificationPayload input.n input.a (enumerate input)

def decodeClassificationPayload (j : Json) : Option (ℕ × ℕ × List EquationData) := do
  let status ← jsonField j "status" >>= decodeJsonString
  if status ≠ "ok" then return ← none
  let input ← jsonField j "input"
  let n ← jsonField input "n" >>= decodeJsonNat
  let a ← jsonField input "a" >>= decodeJsonNat
  let count ← jsonField j "count" >>= decodeJsonNat
  let rows ← jsonField j "equations" >>= decodeJsonList decodeEquationJson
  if count = rows.length then return (n,a,rows) else none

end CanonicalRoots
