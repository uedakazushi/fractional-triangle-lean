import CanonicalRoots.CoxData
import Mathlib.Data.List.Sort

namespace CanonicalRoots
open Cox

/-- Arithmetic witnesses only; membership is not the definition of a root ring. -/
structure TernaryCandidate where
  kind : Kind
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  deriving DecidableEq, BEq, Repr

def candidateWeights (e : TernaryCandidate) : Fin 3 → ℤ :=
  weights e.kind e.alpha e.beta e.gamma

def candidateDegree (e : TernaryCandidate) : ℤ :=
  degree e.kind e.alpha e.beta e.gamma

/-- An independent, unbounded arithmetic predicate. -/
def ArithmeticTernary (a : ℕ) (e : TernaryCandidate) : Prop :=
  2 ≤ e.alpha ∧ 2 ≤ e.beta ∧ 2 ≤ e.gamma ∧
  Int.gcd (candidateWeights e 0) (Int.gcd (candidateWeights e 1) (candidateWeights e 2)) = 1 ∧
  defect e.kind e.alpha e.beta e.gamma = a

instance (a : ℕ) (e : TernaryCandidate) : Decidable (ArithmeticTernary a e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def kinds : List Kind := [.I, .II, .III, .IV, .V]

def ternaryBox (a : ℕ) : List TernaryCandidate :=
  kinds.flatMap fun k => (List.range (a+7)).flatMap fun x =>
    (List.range (a+7)).flatMap fun y => (List.range (a+7)).map fun z => ⟨k,x,y,z⟩

def enumerateTernaryCandidates (a : ℕ) : List TernaryCandidate :=
  (ternaryBox a).filter fun e => decide (ArithmeticTernary a e)

def candidateKey (e : TernaryCandidate) : List ℤ :=
  ([candidateWeights e 0, candidateWeights e 1, candidateWeights e 2].mergeSort (· ≤ ·)) ++
  [candidateDegree e]

/-- Deterministic first representative for each weight key; semantic key theorem is pending. -/
def dedupCandidates (es : List TernaryCandidate) : List TernaryCandidate :=
  es.foldl (fun acc e => if acc.any (fun f => candidateKey f == candidateKey e)
    then acc else acc ++ [e]) []

/-- Structurally recursive higher-dimensional arithmetic search, using Int defects. -/
def higherSearch (a : ℕ) : ℕ → List ℕ → ℤ → ℤ → List (List ℕ)
  | 0, pref, P, A => if 0 < P ∧ A = a then [pref] else []
  | k+1, pref, P, A =>
    if 0 < P ∧ 0 < A then
      let lower := pref.getLast?.getD 1 + 1
      if k = 0 then
        let q := (a+P)/A
        if A ∣ (a+P) ∧ (lower : ℤ) ≤ q ∧
            pref.all (fun t => Nat.Coprime q.toNat t) then [pref ++ [q.toNat]] else []
      else
        let upper := (((k+1+a : ℕ) : ℤ)*P/A).toNat
        ((List.range (upper+1)).filter (fun q => lower ≤ q ∧
          pref.all (fun t => Nat.Coprime q t))).flatMap fun (q : ℕ) =>
            higherSearch a k (pref ++ [q]) (P*(q : ℤ)) (A*(q : ℤ)-P)
    else []

def enumerateHigherCandidates (n a : ℕ) : List (List ℕ) := higherSearch a n [] 1 1

end CanonicalRoots
