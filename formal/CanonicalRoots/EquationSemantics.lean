import CanonicalRoots.Payload
import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Interpret the exact integer data as exponents; well-formedness excludes negative entries. -/
def equationExponent (n : ℕ) (row : List ℤ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (row.getD i.val 0).toNat)

def EquationData.natWeights (e : EquationData) : Fin e.n → ℕ :=
  fun i => (e.weights.getD i.val 0).toNat

/-- The polynomial actually serialized by equationJson has coefficient one on each stored row. -/
def EquationData.polynomial (e : EquationData) : MvPolynomial (Fin e.n) ℂ :=
  (e.exponents.map (fun row => monomial (equationExponent e.n row) 1)).sum

abbrev EquationData.Ring (e : EquationData) := PresentedRing e.polynomial

def EquationData.piece (e : EquationData) (m : ℕ) : Submodule ℂ e.Ring :=
  presentedPiece e.polynomial e.natWeights m

theorem equationExponent_ofFn (n : ℕ) (v : Fin n → ℤ) :
    equationExponent n (List.ofFn v) = Finsupp.equivFunOnFinite.symm (fun i => (v i).toNat) := by
  ext i
  simp [equationExponent, List.getD_eq_getElem, i.isLt]

end CanonicalRoots
