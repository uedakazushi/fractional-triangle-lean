import CanonicalRoots.Final
import Certificates

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
