import CanonicalRoots.Classifier

open Lean CanonicalRoots

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  match args with
  | [ns, as] =>
    match ns.toNat?, as.toNat? with
    | some n, some a =>
      if h : 3 ≤ n ∧ 1 ≤ a then
        out.putStrLn ((classificationPayload ⟨n,a,h.1,h.2⟩).compress)
        return 0
      else
        out.putStrLn ((Json.mkObj [("status",.str "invalid_input"),
          ("message",.str "expected n >= 3 and a >= 1")]).compress)
        return 2
    | _, _ =>
      out.putStrLn ((Json.mkObj [("status",.str "invalid_input"),
        ("message",.str "expected decimal natural numbers")]).compress)
      return 2
  | _ =>
    out.putStrLn ((Json.mkObj [("status",.str "invalid_input"),
      ("message",.str "usage: canonical_roots n a")]).compress)
    return 2
