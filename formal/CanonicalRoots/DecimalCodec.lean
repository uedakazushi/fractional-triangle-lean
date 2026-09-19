import CanonicalRoots.Payload
import Init.Data.Nat.ToString
import Init.Data.Int.ToString

namespace CanonicalRoots

/-- A total decimal parser using Lean's verified digit fold, with explicit syntax checking. -/
def decodeDecimalNatChars (cs : List Char) : Option ℕ :=
  if cs ≠ [] ∧ ∀ c ∈ cs, c.isDigit then some (Nat.ofDigitChars 10 cs 0) else none

def decodeDecimalIntChars (cs : List Char) : Option ℤ :=
  if cs.head? = some '-' then (decodeDecimalNatChars cs.tail).map (fun n => -(n : ℤ))
  else (decodeDecimalNatChars cs).map Int.ofNat

def decodeJsonNat : Lean.Json → Option ℕ
  | .str s => decodeDecimalNatChars s.toList
  | _ => none

def decodeJsonInt : Lean.Json → Option ℤ
  | .str s => decodeDecimalIntChars s.toList
  | _ => none

theorem decodeDecimalNatChars_toDigits (n : ℕ) :
    decodeDecimalNatChars (Nat.toDigits 10 n) = some n := by
  have hd : ∀ c ∈ Nat.toDigits 10 n, c.isDigit :=
    fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  rw [decodeDecimalNatChars, if_pos ⟨Nat.toDigits_ne_nil,hd⟩, Nat.ofDigitChars_ten_toDigits]

theorem toDigits_head_ne_minus (n : ℕ) : (Nat.toDigits 10 n).head? ≠ some '-' := by
  intro h
  have hd := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10)
    (List.mem_of_mem_head? h)
  contradiction

theorem decodeJsonNat_jsonNat (n : ℕ) : decodeJsonNat (jsonNat n) = some n := by
  simpa [decodeJsonNat, jsonNat] using decodeDecimalNatChars_toDigits n

theorem decodeJsonInt_jsonInt (z : ℤ) : decodeJsonInt (jsonInt z) = some z := by
  unfold decodeJsonInt jsonInt
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split_ifs with hz
  · simp [decodeDecimalIntChars, toDigits_head_ne_minus, decodeDecimalNatChars_toDigits,
      Int.toNat_of_nonneg hz]
  · have hz' : 0 ≤ -z := by omega
    simp [String.toList_append, decodeDecimalIntChars, decodeDecimalNatChars_toDigits,
      Int.toNat_of_nonneg hz']

end CanonicalRoots
