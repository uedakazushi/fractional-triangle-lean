import CanonicalRoots.Classifier

namespace CanonicalRoots
open Lean

theorem encodeClassificationPayload_status (n a : ℕ) (rows : List EquationData) :
    jsonField (encodeClassificationPayload n a rows) "status" = some (.str "ok") := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem encodeClassificationPayload_input (n a : ℕ) (rows : List EquationData) :
    jsonField (encodeClassificationPayload n a rows) "input" =
      some (Json.mkObj [("n",jsonNat n),("a",jsonNat a)]) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem encodeClassificationPayload_count (n a : ℕ) (rows : List EquationData) :
    jsonField (encodeClassificationPayload n a rows) "count" = some (jsonNat rows.length) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem encodeClassificationPayload_equations (n a : ℕ) (rows : List EquationData) :
    jsonField (encodeClassificationPayload n a rows) "equations" =
      some (.arr (rows.map equationJson).toArray) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem inputJson_n (n a : ℕ) :
    jsonField (Json.mkObj [("n",jsonNat n),("a",jsonNat a)]) "n" = some (jsonNat n) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem inputJson_a (n a : ℕ) :
    jsonField (Json.mkObj [("n",jsonNat n),("a",jsonNat a)]) "a" = some (jsonNat a) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem decodeClassificationPayload_encode (n a : ℕ) (rows : List EquationData) :
    decodeClassificationPayload (encodeClassificationPayload n a rows) = some (n,a,rows) := by
  simp [decodeClassificationPayload, encodeClassificationPayload_status,
    encodeClassificationPayload_input, encodeClassificationPayload_count,
    encodeClassificationPayload_equations, inputJson_n, inputJson_a, decodeJsonString,
    decodeJsonNat_jsonNat, decodeJsonList_encode _ _ decodeEquationJson_encode]

end CanonicalRoots
