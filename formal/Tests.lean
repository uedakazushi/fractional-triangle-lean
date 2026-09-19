import CanonicalRoots
import Certificates
import OutputCertificates
import CanonicalRoots.HigherRealization

example : ∃ τ : CanonicalRoots.DegreeGroup ![2,3,7,67],
    CanonicalRoots.IsCanonicalRoot ![2,3,7,67] 25 τ ∧
      CanonicalRoots.AdmissibleSignature ![2,3,7,67] ∧
      Nonempty (CanonicalRoots.RootHypersurfacePresentation ![2,3,7,67] τ) := by
  exact CanonicalRoots.higher_root_realization (by decide) _ (by decide +kernel)
    (by decide)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)
    (by decide +kernel)

example : ∃ τ : CanonicalRoots.DegreeGroup ![2,3,7,67],
    CanonicalRoots.IsCanonicalRoot ![2,3,7,67] 5 τ := by
  apply (CanonicalRoots.canonicalRoot_exists_iff _ (by decide +kernel)).mpr
  decide +kernel

namespace CanonicalRoots.Tests
open Certificates

example : (dedupCandidates (enumerateTernaryCandidates 1)).length = 14 := by
  rw [ternary_1_entire_list]; rfl
example : (dedupCandidates (enumerateTernaryCandidates 2)).length = 6 := by
  rw [ternary_2_entire_list]; rfl
example : (dedupCandidates (enumerateTernaryCandidates 3)).length = 8 := by
  rw [ternary_3_entire_list]; rfl
example : (dedupCandidates (enumerateTernaryCandidates 4)).length = 8 := by
  rw [ternary_4_entire_list]; rfl
example : (dedupCandidates (enumerateTernaryCandidates 5)).length = 21 := by
  rw [ternary_5_entire_list]; rfl
example : dedupCandidates (enumerateTernaryCandidates 6) = [] := ternary_6_entire_list

/-- The certificate identifies the entire polynomial-data list, including its variable ordering. -/
theorem equations_3_1_entire_list :
    enumerateCandidateEquations 3 1 = explicitTernary1.map (ternaryEquation 1) := by
  simp only [enumerateCandidateEquations, ↓reduceIte, ternary_1_entire_list]

theorem deletion_rejected :
    dedupCandidates (enumerateTernaryCandidates 1) ≠ explicitTernary1.tail := by
  rw [ternary_1_entire_list]
  decide +kernel

theorem duplication_rejected :
    dedupCandidates (enumerateTernaryCandidates 1) ≠ explicitTernary1 ++ explicitTernary1 := by
  rw [ternary_1_entire_list]
  decide +kernel

end CanonicalRoots.Tests

namespace CanonicalRoots.FinalGateTests

noncomputable section
open CanonicalRoots

def testInput31 : Input := ⟨3,1,by decide,by decide⟩
def testInput36 : Input := ⟨3,6,by decide,by decide⟩
def testInput41 : Input := ⟨4,1,by decide,by decide⟩

example : (enumerate testInput31).length = 14 := by
  simp [enumerate, testInput31, enumerateCandidateEquations, Certificates.ternary_1_entire_list,
    Certificates.explicitTernary1]

example : enumerate testInput36 = [] := by
  simp [enumerate, testInput36, enumerateCandidateEquations, Certificates.ternary_6_entire_list,
    Certificates.explicitTernary6]

example : enumerate testInput41 = [higherEquation 1 [2,3,7,43]] := by
  simp [enumerate, testInput41, enumerateCandidateEquations, Certificates.higher_4_1_entire_list]

example (input : Input) (e : EquationData) (he : e ∈ enumerate input) : EquationRealizes input e :=
  enumerate_sound input e he

example (input : Input) (t : Target input.n input.a) :
    ∃! i : Fin (enumerate input).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau) ((enumerate input).get i).piece) :=
  enumerate_complete input t

example (input : Input) (i j : Fin (enumerate input).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv ((enumerate input).get i).piece ((enumerate input).get j).piece) :=
  enumerate_pairwise_nonisomorphic input i j hij

example (input : Input) : decodeClassificationPayload (classificationPayload input) =
    some (input.n,input.a,enumerate input) := cli_payload_correct input

example : IsEmpty (Target 3 6) := by
  refine ⟨fun t => ?_⟩
  obtain ⟨i,_,_⟩ := enumerate_complete testInput36 t
  have hi := i.isLt
  simp [enumerate, testInput36, enumerateCandidateEquations, Certificates.ternary_6_entire_list,
    Certificates.explicitTernary6] at hi

end
end CanonicalRoots.FinalGateTests

namespace CanonicalRoots.CertificateMutationTests
open OutputCertificates

example : checkEquationList n3_a1_input n3_a1_rows = true :=
  (checkEquationList_correct _ _).mpr n3_a1_entire_list.symm

example : checkEquationList n3_a1_input n3_a1_rows.tail = false := by
  simp only [checkEquationList, n3_a1_entire_list]
  decide +kernel

example : checkEquationList n3_a1_input (n3_a1_rows ++ n3_a1_rows) = false := by
  simp only [checkEquationList, n3_a1_entire_list]
  decide +kernel

example : checkEquationList n4_a1_input
    (n4_a1_rows.map fun e => { e with exponents := [[2,0,0,0],[0,3,0,0],[0,0,7,0],[0,0,0,43]] }) = false := by
  simp only [checkEquationList, n4_a1_entire_list]
  decide +kernel

example : checkEquationList n4_a1_input
    (n4_a1_rows.map fun e => { e with relationDegree := 2815 }) = false := by
  simp only [checkEquationList, n4_a1_entire_list]
  decide +kernel

example : decodePolynomialTerm (Lean.Json.mkObj [("coefficient",jsonInt 2),
    ("exponents",jsonInts [1,2,3])]) = none := by decide +kernel

end CanonicalRoots.CertificateMutationTests
