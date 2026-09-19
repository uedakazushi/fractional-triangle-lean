import CanonicalRoots.ClassificationPayloadCodec

open CanonicalRoots Lean

example : decodeJsonNat (jsonNat 90071992547409930000000000000000001) =
    some 90071992547409930000000000000000001 := decodeJsonNat_jsonNat _
example : decodeJsonInt (jsonInt (-90071992547409930000000000000000001)) =
    some (-90071992547409930000000000000000001) := decodeJsonInt_jsonInt _
example : decodeJsonNat (.str "-1") = none := by decide +kernel
example : decodeJsonInt (.str "") = none := by decide +kernel
example : decodeJsonInt (.str "12x3") = none := by decide +kernel
example : decodePolynomialTerm (Json.mkObj [("coefficient",jsonInt 2),("exponents",jsonInts [1,2,3])]) =
    none := by decide +kernel

example (e : EquationData) : decodeEquationJson (equationJson e) = some e := decodeEquationJson_encode e
example (n a : ℕ) (rows : List EquationData) :
    decodeClassificationPayload (encodeClassificationPayload n a rows) = some (n,a,rows) :=
  decodeClassificationPayload_encode n a rows

example : decodeClassificationPayload (encodeClassificationPayload 3 6 []) = some (3,6,[]) :=
  decodeClassificationPayload_encode 3 6 []
