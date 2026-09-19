import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.GCD

/- Universal polynomial identities. These are not the classification bridge. -/
namespace CanonicalRoots.Cox
open Matrix

inductive Kind | I | II | III | IV | V
  deriving DecidableEq, Repr, BEq

abbrev Vec := Fin 3 → ℤ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

def weights (k : Kind) (a b c : ℤ) : Vec :=
  match k with
  | .I => ![b*c, a*c, a*b]
  | .II => ![c*(b-1), a*c, a*b]
  | .III => ![c*(b-1), c*(a-1), a*b-1]
  | .IV => ![c*(b-1)+1, a*(c-1), a*b]
  | .V => ![c*(b-1)+1, a*(c-1)+1, b*(a-1)+1]

def degree (k : Kind) (a b c : ℤ) : ℤ :=
  match k with
  | .I | .II | .IV => a*b*c
  | .III => c*(a*b-1)
  | .V => a*b*c+1

def signature (k : Kind) (a b c : ℤ) : Vec :=
  match k with
  | .I => ![a,b,c]
  | .II => ![a,c*(b-1),c]
  | .III => ![c*(a-1),c*(b-1),c]
  | .IV => ![a,c*(b-1)+1,a*(c-1)]
  | .V => ![b*(a-1)+1,c*(b-1)+1,a*(c-1)+1]

def exponents (k : Kind) (a b c : ℤ) : Mat :=
  match k with
  | .I => !![a,0,0; 0,b,0; 0,0,c]
  | .II => !![a,1,0; 0,b,0; 0,0,c]
  | .III => !![a,1,0; 1,b,0; 0,0,c]
  | .IV => !![a,1,0; 0,b,1; 0,0,c]
  | .V => !![a,1,0; 0,b,1; 1,0,c]

def monomials (k : Kind) (a b c : ℤ) : Mat :=
  match k with
  | .I => !![1,0,0; 0,1,0; 0,0,1]
  | .II => !![1,0,0; 0,c,0; 0,1,1]
  | .III => !![c,0,0; 0,c,0; 1,1,1]
  | .IV => !![1,0,1; 0,c,0; 0,1,a]
  | .V => !![b,0,1; 1,c,0; 0,1,a]

def common (k : Kind) (a b c : ℤ) : Vec :=
  match k with
  | .I => ![0,0,0]
  | .II => ![0,c,0]
  | .III => ![c,c,0]
  | .IV => ![0,c,a]
  | .V => ![b,c,a]

def certificate (k : Kind) (a b c : ℤ) : Mat :=
  match k with
  | .I => !![b*c-b-c,c,b; c,a*c-a-c,a; b,a,a*b-a-b]
  | .II => !![b*c-b-c,1,b-1; c,a*c-a-c,a; b,a-1,a*b-a-b+1]
  | .III => !![b*c-b-c,1,b-1; 1,a*c-a-c,a-1; b-1,a-1,a*b-a-b+1]
  | .IV => !![b*c-b-c+1,1,b-1; c-1,a*c-a-c,1; b,a-1,a*b-a-b+1]
  | .V => !![b*c-b-c+1,1,b-1; c-1,a*c-a-c+1,1; 1,a-1,a*b-a-b+1]

def defect (k : Kind) (a b c : ℤ) : ℤ :=
  degree k a b c - ∑ i, weights k a b c i


end CanonicalRoots.Cox
