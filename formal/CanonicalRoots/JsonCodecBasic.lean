import CanonicalRoots.DecimalCodec
import Std.Data.TreeMap.Raw.Lemmas

namespace CanonicalRoots
open Lean

def jsonField (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

theorem jsonField_mkObj_of_mem (xs : List (String × Json)) (k : String) (v : Json)
    (hd : xs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) (hm : (k,v) ∈ xs) :
    jsonField (Json.mkObj xs) k = some v := by
  unfold jsonField Json.mkObj Json.getObjVal?
  dsimp only
  rw [Std.TreeMap.Raw.get?_eq_getElem?,
    Std.TreeMap.Raw.getElem?_ofList_of_mem (show compare k k = .eq from by simp) hd hm]
  rfl

def decodeJsonString : Json → Option String
  | .str s => some s
  | _ => none

def decodeJsonList {α : Type} (decode : Json → Option α) : Json → Option (List α)
  | .arr xs => xs.toList.mapM decode
  | _ => none

theorem decodeJsonList_encode {α : Type} (decode : Json → Option α) (encode : α → Json)
    (hc : ∀ x, decode (encode x) = some x) (xs : List α) :
    decodeJsonList decode (.arr (xs.map encode).toArray) = some xs := by
  simp only [decodeJsonList, List.toList_toArray]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [hc, ih]

theorem decodeJsonList_jsonInts (xs : List ℤ) : decodeJsonList decodeJsonInt (jsonInts xs) = some xs :=
  decodeJsonList_encode _ _ decodeJsonInt_jsonInt xs

theorem equationJson_n (e : EquationData) : jsonField (equationJson e) "n" = some (jsonNat e.n) := by
  apply jsonField_mkObj_of_mem
  · simp [List.pairwise_cons]
  · simp

end CanonicalRoots
