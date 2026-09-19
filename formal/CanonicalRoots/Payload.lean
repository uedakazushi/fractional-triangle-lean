import CanonicalRoots.CandidateData
import Lean.Data.Json

namespace CanonicalRoots
open Lean

/-- Exact finite polynomial data; the semantic classification is not asserted by this record. -/
structure EquationData where
  n : ℕ
  a : ℕ
  weights : List ℤ
  relationDegree : ℤ
  exponents : List (List ℤ)
  orderedSignature : List ℤ
  monomialMatrix : List (List ℤ)
  commonMonomial : List ℤ
  variableOrder : List ℕ
  tag : String
  deriving BEq, Repr, DecidableEq

def ternaryEquation (a : ℕ) (e : TernaryCandidate) : EquationData :=
  let w := candidateWeights e
  let order := (List.finRange 3).mergeSort fun i j => w i ≤ w j
  { n := 3, a := a, weights := order.map w, relationDegree := candidateDegree e
    exponents := (List.finRange 3).map fun i => order.map fun j => Cox.exponents e.kind e.alpha e.beta e.gamma i j
    orderedSignature := (List.finRange 3).map (Cox.signature e.kind e.alpha e.beta e.gamma)
    monomialMatrix := order.map fun i => (List.finRange 3).map (Cox.monomials e.kind e.alpha e.beta e.gamma i)
    commonMonomial := (List.finRange 3).map (Cox.common e.kind e.alpha e.beta e.gamma)
    variableOrder := order.map Fin.val
    tag := match e.kind with | .I => "I" | .II => "II" | .III => "III" | .IV => "IV" | .V => "V" }

def higherEquation (a : ℕ) (ps : List ℕ) : EquationData :=
  let p := ps.toArray
  let P : ℤ := (ps.map Int.ofNat).prod
  let ids := List.range ps.length
  let w := fun j => P / (Int.ofNat (p[j]?.getD 1))
  let order := ids.mergeSort fun i j => w i ≤ w j
  { n := ps.length, a := a, weights := order.map w, relationDegree := P
    exponents := ids.map fun i => order.map fun j => if i=j then (Int.ofNat (p[i]?.getD 0)) else 0
    orderedSignature := ps.map Int.ofNat
    monomialMatrix := order.map fun i => ids.map fun j => if i=j then 1 else 0
    commonMonomial := ids.map fun _ => 0, variableOrder := order, tag := "Fermat" }

def enumerateCandidateEquations (n a : ℕ) : List EquationData :=
  if n = 3 then (dedupCandidates (enumerateTernaryCandidates a)).map (ternaryEquation a)
  else (enumerateHigherCandidates n a).map (higherEquation a)

def jsonInt (n : ℤ) : Json := .str (toString n)
def jsonNat (n : ℕ) : Json := .str (toString n)
def jsonInts (ns : List ℤ) : Json := .arr (ns.map jsonInt).toArray

def rootWitnessJson (a : ℕ) (p : List ℤ) : Json :=
  let residues : List ℕ := p.map fun q => ((List.range q.toNat).find? fun (s : ℕ) => ((a : ℤ)*(s : ℤ)+1)%q=0).getD 0
  let carries := (p.zip residues).map fun (q,s) => ((a : ℤ)*(Int.ofNat s)+1)/q
  Json.mkObj [("c_coefficient", jsonInt ((1-carries.sum)/(a : ℤ))),
    ("residues", .arr (residues.map jsonNat).toArray), ("signature_order",jsonInts p)]

def equationJson (e : EquationData) : Json := Json.mkObj
  [("n",jsonNat e.n), ("a",jsonNat e.a), ("weights",jsonInts e.weights),
   ("relation_degree",jsonInt e.relationDegree),
   ("weight_key",jsonInts (e.weights ++ [e.relationDegree])),
   ("polynomial", .arr (e.exponents.map fun row => Json.mkObj
     [("coefficient",jsonInt 1),("exponents",jsonInts row)]).toArray),
   ("signature",jsonInts (e.orderedSignature.mergeSort (· ≤ ·))),
   ("root",rootWitnessJson e.a e.orderedSignature),
   ("witness",Json.mkObj [("ordered_signature",jsonInts e.orderedSignature),
     ("monomial_matrix",.arr (e.monomialMatrix.map jsonInts).toArray),
     ("common_monomial",jsonInts e.commonMonomial),
     ("generator_permutation_new_to_old",.arr (e.variableOrder.map jsonNat).toArray),
     ("standard_form_tag",.str e.tag)])]

/-- Incomplete status is deliberate until all semantic final theorems are proved. -/
def candidatePayload (n a : ℕ) : Json :=
  let rows := enumerateCandidateEquations n a
  Json.mkObj [("schema",.str "canonical-root-candidates-v1"),
    ("status",.str "incomplete"),
    ("verification_status",.str "SEMANTIC_CLASSIFICATION_NOT_PROVED"),
    ("integer_encoding",.str "decimal strings"),
    ("input",Json.mkObj [("n",jsonNat n),("a",jsonNat a)]),
    ("count",jsonNat rows.length), ("equations",.arr (rows.map equationJson).toArray)]

end CanonicalRoots
