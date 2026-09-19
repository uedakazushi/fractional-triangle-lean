import CanonicalRoots.EquationJsonFields

namespace CanonicalRoots
open Lean

def decodePolynomialTerm (j : Json) : Option (List ℤ) := do
  let c ← jsonField j "coefficient" >>= decodeJsonInt
  if c = 1 then jsonField j "exponents" >>= decodeJsonList decodeJsonInt else none

/-- Decode every field of EquationData, including the unsorted signature and monomial witness. -/
def decodeEquationJson (j : Json) : Option EquationData := do
  let n ← jsonField j "n" >>= decodeJsonNat
  let a ← jsonField j "a" >>= decodeJsonNat
  let w ← jsonField j "weights" >>= decodeJsonList decodeJsonInt
  let h ← jsonField j "relation_degree" >>= decodeJsonInt
  let E ← jsonField j "polynomial" >>= decodeJsonList decodePolynomialTerm
  let witness ← jsonField j "witness"
  let p ← jsonField witness "ordered_signature" >>= decodeJsonList decodeJsonInt
  let B ← jsonField witness "monomial_matrix" >>= decodeJsonList (decodeJsonList decodeJsonInt)
  let c ← jsonField witness "common_monomial" >>= decodeJsonList decodeJsonInt
  let order ← jsonField witness "generator_permutation_new_to_old" >>= decodeJsonList decodeJsonNat
  let tag ← jsonField witness "standard_form_tag" >>= decodeJsonString
  return ⟨n,a,w,h,E,p,B,c,order,tag⟩

theorem decodePolynomialTerm_encode (row : List ℤ) :
    decodePolynomialTerm (polynomialTermJson row) = some row := by
  simp [decodePolynomialTerm, polynomialTermJson_coefficient, polynomialTermJson_exponents,
    decodeJsonInt_jsonInt, decodeJsonList_jsonInts]

/-- Pure JSON decoding recovers the exact unbounded integer data in every equation record. -/
theorem decodeEquationJson_encode (e : EquationData) : decodeEquationJson (equationJson e) = some e := by
  simp [decodeEquationJson, equationJson_n, equationJson_a, equationJson_weights,
    equationJson_relationDegree, equationJson_polynomial, equationJson_witness,
    equationWitnessJson_signature, equationWitnessJson_matrix, equationWitnessJson_common,
    equationWitnessJson_permutation, equationWitnessJson_tag,
    Option.bind_some, decodeJsonNat_jsonNat, decodeJsonInt_jsonInt, decodeJsonList_jsonInts,
    decodeJsonList_encode _ _ decodePolynomialTerm_encode,
    decodeJsonList_encode _ _ decodeJsonList_jsonInts,
    decodeJsonList_encode _ _ decodeJsonNat_jsonNat, decodeJsonString]

end CanonicalRoots
