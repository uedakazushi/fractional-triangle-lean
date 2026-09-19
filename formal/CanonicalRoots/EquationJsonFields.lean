import CanonicalRoots.JsonCodecBasic

namespace CanonicalRoots
open Lean

def equationWitnessJson (e : EquationData) : Json := Json.mkObj
  [("ordered_signature",jsonInts e.orderedSignature),
   ("monomial_matrix",.arr (e.monomialMatrix.map jsonInts).toArray),
   ("common_monomial",jsonInts e.commonMonomial),
   ("generator_permutation_new_to_old",.arr (e.variableOrder.map jsonNat).toArray),
   ("standard_form_tag",.str e.tag)]

def polynomialTermJson (row : List ℤ) : Json :=
  Json.mkObj [("coefficient",jsonInt 1),("exponents",jsonInts row)]

theorem equationJson_a (e : EquationData) : jsonField (equationJson e) "a" = some (jsonNat e.a) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem equationJson_weights (e : EquationData) :
    jsonField (equationJson e) "weights" = some (jsonInts e.weights) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem equationJson_relationDegree (e : EquationData) :
    jsonField (equationJson e) "relation_degree" = some (jsonInt e.relationDegree) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem equationJson_polynomial (e : EquationData) :
    jsonField (equationJson e) "polynomial" = some (.arr (e.exponents.map polynomialTermJson).toArray) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons, polynomialTermJson]

theorem equationJson_witness (e : EquationData) :
    jsonField (equationJson e) "witness" = some (equationWitnessJson e) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons, equationWitnessJson]

theorem equationWitnessJson_signature (e : EquationData) :
    jsonField (equationWitnessJson e) "ordered_signature" = some (jsonInts e.orderedSignature) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem equationWitnessJson_matrix (e : EquationData) :
    jsonField (equationWitnessJson e) "monomial_matrix" = some (.arr (e.monomialMatrix.map jsonInts).toArray) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem equationWitnessJson_common (e : EquationData) :
    jsonField (equationWitnessJson e) "common_monomial" = some (jsonInts e.commonMonomial) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem equationWitnessJson_permutation (e : EquationData) :
    jsonField (equationWitnessJson e) "generator_permutation_new_to_old" = some (.arr (e.variableOrder.map jsonNat).toArray) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem equationWitnessJson_tag (e : EquationData) :
    jsonField (equationWitnessJson e) "standard_form_tag" = some (.str e.tag) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem polynomialTermJson_coefficient (row : List ℤ) :
    jsonField (polynomialTermJson row) "coefficient" = some (jsonInt 1) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

theorem polynomialTermJson_exponents (row : List ℤ) :
    jsonField (polynomialTermJson row) "exponents" = some (jsonInts row) := by
  apply jsonField_mkObj_of_mem <;> simp [List.pairwise_cons]

end CanonicalRoots
