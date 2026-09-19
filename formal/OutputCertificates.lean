import CanonicalRoots.OutputCertificateChecker
import Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CanonicalRoots.OutputCertificates

def n3_a1_input : Input := ⟨3,1,by decide,by decide⟩
def n3_a1_rows : List EquationData :=
  [⟨3, 1, [6,14,21], 42, [[0,0,2],[0,3,0],[7,0,0]], [2,3,7], [[0,0,1],[0,1,0],[1,0,0]], [0,0,0], [2,1,0], "I"⟩,
   ⟨3, 1, [4,5,10], 20, [[0,2,1],[0,0,2],[5,0,0]], [2,5,5], [[0,1,1],[1,0,0],[0,5,0]], [0,5,0], [2,0,1], "II"⟩,
   ⟨3, 1, [6,8,9], 24, [[1,0,2],[4,0,0],[0,3,0]], [2,9,3], [[0,3,0],[0,1,1],[1,0,0]], [0,3,0], [1,2,0], "II"⟩,
   ⟨3, 1, [6,8,15], 30, [[1,3,0],[5,0,0],[0,0,2]], [3,8,2], [[0,2,0],[1,0,0],[0,1,1]], [0,2,0], [1,0,2], "II"⟩,
   ⟨3, 1, [3,8,12], 24, [[4,0,1],[0,0,2],[0,3,0]], [4,3,3], [[1,0,0],[0,1,1],[0,3,0]], [0,3,0], [0,2,1], "II"⟩,
   ⟨3, 1, [4,10,15], 30, [[5,1,0],[0,3,0],[0,0,2]], [5,4,2], [[1,0,0],[0,2,0],[0,1,1]], [0,2,0], [0,1,2], "II"⟩,
   ⟨3, 1, [3,4,4], 12, [[0,2,1],[0,1,2],[4,0,0]], [4,4,4], [[1,1,1],[4,0,0],[0,4,0]], [4,4,0], [2,0,1], "III"⟩,
   ⟨3, 1, [3,5,6], 15, [[1,0,2],[3,0,1],[0,3,0]], [3,6,3], [[0,3,0],[1,1,1],[3,0,0]], [3,3,0], [1,2,0], "III"⟩,
   ⟨3, 1, [4,6,11], 22, [[1,3,0],[4,1,0],[0,0,2]], [4,6,2], [[0,2,0],[2,0,0],[1,1,1]], [2,2,0], [1,0,2], "III"⟩,
   ⟨3, 1, [4,5,6], 16, [[0,2,1],[1,0,2],[4,0,0]], [2,5,6], [[0,1,2],[1,0,1],[0,4,0]], [0,4,2], [2,0,1], "IV"⟩,
   ⟨3, 1, [4,6,7], 18, [[1,0,2],[3,1,0],[0,3,0]], [2,7,4], [[0,3,0],[0,1,2],[1,0,1]], [0,3,2], [1,2,0], "IV"⟩,
   ⟨3, 1, [3,5,9], 18, [[1,3,0],[3,0,1],[0,0,2]], [3,5,3], [[0,2,0],[1,0,1],[0,1,3]], [0,2,3], [1,0,2], "IV"⟩,
   ⟨3, 1, [3,4,8], 16, [[4,1,0],[0,2,1],[0,0,2]], [4,3,4], [[1,0,1],[0,2,0],[0,1,4]], [0,2,4], [0,1,2], "IV"⟩,
   ⟨3, 1, [3,4,5], 13, [[0,2,1],[1,0,2],[3,1,0]], [3,4,5], [[0,1,2],[2,0,1],[1,3,0]], [2,3,2], [2,0,1], "V"⟩]

theorem n3_a1_entire_list : enumerate n3_a1_input = n3_a1_rows := by
  change enumerateCandidateEquations 3 1 = _
  rw [enumerateCandidateEquations, if_pos rfl, Certificates.ternary_1_entire_list]
  cbv

theorem n3_a1_payload : decodeClassificationPayload (classificationPayload n3_a1_input) =
    some (3,1,n3_a1_rows) := by
  rw [cli_payload_correct, n3_a1_entire_list]
  rfl

def n3_a2_input : Input := ⟨3,2,by decide,by decide⟩
def n3_a2_rows : List EquationData :=
  [⟨3, 2, [3,10,15], 30, [[5,0,1],[0,0,2],[0,3,0]], [5,3,3], [[1,0,0],[0,1,1],[0,3,0]], [0,3,0], [0,2,1], "II"⟩,
   ⟨3, 2, [3,5,5], 15, [[0,2,1],[0,1,2],[5,0,0]], [5,5,5], [[1,1,1],[5,0,0],[0,5,0]], [5,5,0], [2,0,1], "III"⟩,
   ⟨3, 2, [3,7,9], 21, [[1,0,2],[4,0,1],[0,3,0]], [3,9,3], [[0,3,0],[1,1,1],[3,0,0]], [3,3,0], [1,2,0], "III"⟩,
   ⟨3, 2, [3,7,12], 24, [[1,3,0],[4,0,1],[0,0,2]], [3,7,3], [[0,2,0],[1,0,1],[0,1,3]], [0,2,3], [1,0,2], "IV"⟩,
   ⟨3, 2, [3,5,10], 20, [[5,1,0],[0,2,1],[0,0,2]], [5,3,5], [[1,0,1],[0,2,0],[0,1,5]], [0,2,5], [0,1,2], "IV"⟩,
   ⟨3, 2, [3,5,7], 17, [[0,2,1],[1,0,2],[4,1,0]], [3,5,7], [[0,1,2],[2,0,1],[1,4,0]], [2,4,2], [2,0,1], "V"⟩]

theorem n3_a2_entire_list : enumerate n3_a2_input = n3_a2_rows := by
  change enumerateCandidateEquations 3 2 = _
  rw [enumerateCandidateEquations, if_pos rfl, Certificates.ternary_2_entire_list]
  cbv

theorem n3_a2_payload : decodeClassificationPayload (classificationPayload n3_a2_input) =
    some (3,2,n3_a2_rows) := by
  rw [cli_payload_correct, n3_a2_entire_list]
  rfl

def n3_a3_input : Input := ⟨3,3,by decide,by decide⟩
def n3_a3_rows : List EquationData :=
  [⟨3, 3, [4,7,14], 28, [[0,2,1],[0,0,2],[7,0,0]], [2,7,7], [[0,1,1],[1,0,0],[0,7,0]], [0,7,0], [2,0,1], "II"⟩,
   ⟨3, 3, [4,14,21], 42, [[7,1,0],[0,3,0],[0,0,2]], [7,4,2], [[1,0,0],[0,2,0],[0,1,1]], [0,2,0], [0,1,2], "II"⟩,
   ⟨3, 3, [4,5,8], 20, [[1,0,2],[3,0,1],[0,4,0]], [4,8,4], [[0,4,0],[1,1,1],[4,0,0]], [4,4,0], [1,2,0], "III"⟩,
   ⟨3, 3, [4,10,17], 34, [[1,3,0],[6,1,0],[0,0,2]], [4,10,2], [[0,2,0],[2,0,0],[1,1,1]], [2,2,0], [1,0,2], "III"⟩,
   ⟨3, 3, [4,7,10], 24, [[0,2,1],[1,0,2],[6,0,0]], [2,7,10], [[0,1,2],[1,0,1],[0,6,0]], [0,6,2], [2,0,1], "IV"⟩,
   ⟨3, 3, [4,10,13], 30, [[1,0,2],[5,1,0],[0,3,0]], [2,13,4], [[0,3,0],[0,1,2],[1,0,1]], [0,3,2], [1,2,0], "IV"⟩,
   ⟨3, 3, [4,5,12], 24, [[1,4,0],[3,0,1],[0,0,2]], [4,5,4], [[0,2,0],[1,0,1],[0,1,4]], [0,2,4], [1,0,2], "IV"⟩,
   ⟨3, 3, [4,5,7], 19, [[0,1,2],[1,3,0],[3,0,1]], [4,7,5], [[0,1,2],[1,3,0],[3,0,1]], [3,3,2], [2,1,0], "V"⟩]

theorem n3_a3_entire_list : enumerate n3_a3_input = n3_a3_rows := by
  change enumerateCandidateEquations 3 3 = _
  rw [enumerateCandidateEquations, if_pos rfl, Certificates.ternary_3_entire_list]
  cbv

theorem n3_a3_payload : decodeClassificationPayload (classificationPayload n3_a3_input) =
    some (3,3,n3_a3_rows) := by
  rw [cli_payload_correct, n3_a3_entire_list]
  rfl

def n3_a4_input : Input := ⟨3,4,by decide,by decide⟩
def n3_a4_rows : List EquationData :=
  [⟨3, 4, [5,6,15], 30, [[3,0,1],[0,0,2],[0,5,0]], [3,5,5], [[1,0,0],[0,1,1],[0,5,0]], [0,5,0], [0,2,1], "II"⟩,
   ⟨3, 4, [3,14,21], 42, [[7,0,1],[0,0,2],[0,3,0]], [7,3,3], [[1,0,0],[0,1,1],[0,3,0]], [0,3,0], [0,2,1], "II"⟩,
   ⟨3, 4, [3,7,7], 21, [[0,2,1],[0,1,2],[7,0,0]], [7,7,7], [[1,1,1],[7,0,0],[0,7,0]], [7,7,0], [2,0,1], "III"⟩,
   ⟨3, 4, [3,11,15], 33, [[1,0,2],[6,0,1],[0,3,0]], [3,15,3], [[0,3,0],[1,1,1],[3,0,0]], [3,3,0], [1,2,0], "III"⟩,
   ⟨3, 4, [5,6,9], 24, [[3,0,1],[0,1,2],[0,4,0]], [3,5,9], [[1,0,1],[0,1,3],[0,4,0]], [0,4,3], [0,2,1], "IV"⟩,
   ⟨3, 4, [3,11,18], 36, [[1,3,0],[6,0,1],[0,0,2]], [3,11,3], [[0,2,0],[1,0,1],[0,1,3]], [0,2,3], [1,0,2], "IV"⟩,
   ⟨3, 4, [3,7,14], 28, [[7,1,0],[0,2,1],[0,0,2]], [7,3,7], [[1,0,1],[0,2,0],[0,1,7]], [0,2,7], [0,1,2], "IV"⟩,
   ⟨3, 4, [3,7,11], 25, [[0,2,1],[1,0,2],[6,1,0]], [3,7,11], [[0,1,2],[2,0,1],[1,6,0]], [2,6,2], [2,0,1], "V"⟩]

theorem n3_a4_entire_list : enumerate n3_a4_input = n3_a4_rows := by
  change enumerateCandidateEquations 3 4 = _
  rw [enumerateCandidateEquations, if_pos rfl, Certificates.ternary_4_entire_list]
  cbv

theorem n3_a4_payload : decodeClassificationPayload (classificationPayload n3_a4_input) =
    some (3,4,n3_a4_rows) := by
  rw [cli_payload_correct, n3_a4_entire_list]
  rfl

def n3_a5_input : Input := ⟨3,5,by decide,by decide⟩
def n3_a5_rows : List EquationData :=
  [⟨3, 5, [6,22,33], 66, [[0,0,2],[0,3,0],[11,0,0]], [2,3,11], [[0,0,1],[0,1,0],[1,0,0]], [0,0,0], [2,1,0], "I"⟩,
   ⟨3, 5, [4,9,18], 36, [[0,2,1],[0,0,2],[9,0,0]], [2,9,9], [[0,1,1],[1,0,0],[0,9,0]], [0,9,0], [2,0,1], "II"⟩,
   ⟨3, 5, [6,16,21], 48, [[1,0,2],[8,0,0],[0,3,0]], [2,21,3], [[0,3,0],[0,1,1],[1,0,0]], [0,3,0], [1,2,0], "II"⟩,
   ⟨3, 5, [6,16,27], 54, [[1,3,0],[9,0,0],[0,0,2]], [3,16,2], [[0,2,0],[1,0,0],[0,1,1]], [0,2,0], [1,0,2], "II"⟩,
   ⟨3, 5, [3,16,24], 48, [[8,0,1],[0,0,2],[0,3,0]], [8,3,3], [[1,0,0],[0,1,1],[0,3,0]], [0,3,0], [0,2,1], "II"⟩,
   ⟨3, 5, [4,18,27], 54, [[9,1,0],[0,3,0],[0,0,2]], [9,4,2], [[1,0,0],[0,2,0],[0,1,1]], [0,2,0], [0,1,2], "II"⟩,
   ⟨3, 5, [3,8,8], 24, [[0,2,1],[0,1,2],[8,0,0]], [8,8,8], [[1,1,1],[8,0,0],[0,8,0]], [8,8,0], [2,0,1], "III"⟩,
   ⟨3, 5, [4,7,12], 28, [[1,0,2],[4,0,1],[0,4,0]], [4,12,4], [[0,4,0],[1,1,1],[4,0,0]], [4,4,0], [1,2,0], "III"⟩,
   ⟨3, 5, [3,13,18], 39, [[1,0,2],[7,0,1],[0,3,0]], [3,18,3], [[0,3,0],[1,1,1],[3,0,0]], [3,3,0], [1,2,0], "III"⟩,
   ⟨3, 5, [4,14,23], 46, [[1,3,0],[8,1,0],[0,0,2]], [4,14,2], [[0,2,0],[2,0,0],[1,1,1]], [2,2,0], [1,0,2], "III"⟩,
   ⟨3, 5, [6,8,19], 38, [[1,4,0],[5,1,0],[0,0,2]], [6,8,2], [[0,2,0],[2,0,0],[1,1,1]], [2,2,0], [1,0,2], "III"⟩,
   ⟨3, 5, [4,9,14], 32, [[0,2,1],[1,0,2],[8,0,0]], [2,9,14], [[0,1,2],[1,0,1],[0,8,0]], [0,8,2], [2,0,1], "IV"⟩,
   ⟨3, 5, [6,8,11], 30, [[0,1,2],[1,3,0],[5,0,0]], [2,11,8], [[0,1,2],[0,5,0],[1,0,1]], [0,5,2], [2,1,0], "IV"⟩,
   ⟨3, 5, [6,8,13], 32, [[1,0,2],[4,1,0],[0,4,0]], [2,13,6], [[0,4,0],[0,1,2],[1,0,1]], [0,4,2], [1,2,0], "IV"⟩,
   ⟨3, 5, [4,14,19], 42, [[1,0,2],[7,1,0],[0,3,0]], [2,19,4], [[0,3,0],[0,1,2],[1,0,1]], [0,3,2], [1,2,0], "IV"⟩,
   ⟨3, 5, [6,7,9], 27, [[1,3,0],[3,0,1],[0,0,3]], [3,7,6], [[0,3,0],[1,0,1],[0,1,3]], [0,3,3], [1,0,2], "IV"⟩,
   ⟨3, 5, [3,13,21], 42, [[1,3,0],[7,0,1],[0,0,2]], [3,13,3], [[0,2,0],[1,0,1],[0,1,3]], [0,2,3], [1,0,2], "IV"⟩,
   ⟨3, 5, [4,7,16], 32, [[1,4,0],[4,0,1],[0,0,2]], [4,7,4], [[0,2,0],[1,0,1],[0,1,4]], [0,2,4], [1,0,2], "IV"⟩,
   ⟨3, 5, [3,8,16], 32, [[8,1,0],[0,2,1],[0,0,2]], [8,3,8], [[1,0,1],[0,2,0],[0,1,8]], [0,2,8], [0,1,2], "IV"⟩,
   ⟨3, 5, [3,8,13], 29, [[0,2,1],[1,0,2],[7,1,0]], [3,8,13], [[0,1,2],[2,0,1],[1,7,0]], [2,7,2], [2,0,1], "V"⟩,
   ⟨3, 5, [4,7,9], 25, [[0,1,2],[1,3,0],[4,0,1]], [4,9,7], [[0,1,2],[1,4,0],[3,0,1]], [3,4,2], [2,1,0], "V"⟩]

theorem n3_a5_entire_list : enumerate n3_a5_input = n3_a5_rows := by
  change enumerateCandidateEquations 3 5 = _
  rw [enumerateCandidateEquations, if_pos rfl, Certificates.ternary_5_entire_list]
  cbv

theorem n3_a5_payload : decodeClassificationPayload (classificationPayload n3_a5_input) =
    some (3,5,n3_a5_rows) := by
  rw [cli_payload_correct, n3_a5_entire_list]
  rfl

def n3_a6_input : Input := ⟨3,6,by decide,by decide⟩
def n3_a6_rows : List EquationData :=
  []

theorem n3_a6_entire_list : enumerate n3_a6_input = n3_a6_rows := by
  change enumerateCandidateEquations 3 6 = _
  rw [enumerateCandidateEquations, if_pos rfl, Certificates.ternary_6_entire_list]
  cbv

theorem n3_a6_payload : decodeClassificationPayload (classificationPayload n3_a6_input) =
    some (3,6,n3_a6_rows) := by
  rw [cli_payload_correct, n3_a6_entire_list]
  rfl

def n4_a1_input : Input := ⟨4,1,by decide,by decide⟩
def n4_a1_rows : List EquationData :=
  [⟨4, 1, [42,258,602,903], 1806, [[0,0,0,2],[0,0,3,0],[0,7,0,0],[43,0,0,0]], [2,3,7,43], [[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]], [0,0,0,0], [3,2,1,0], "Fermat"⟩]

theorem n4_a1_entire_list : enumerate n4_a1_input = n4_a1_rows := by
  change enumerateCandidateEquations 4 1 = _
  rw [enumerateCandidateEquations, if_neg (by decide), Certificates.higher_4_1_entire_list]
  cbv

theorem n4_a1_payload : decodeClassificationPayload (classificationPayload n4_a1_input) =
    some (4,1,n4_a1_rows) := by
  rw [cli_payload_correct, n4_a1_entire_list]
  rfl

def n4_a5_input : Input := ⟨4,5,by decide,by decide⟩
def n4_a5_rows : List EquationData :=
  [⟨4, 5, [42,282,658,987], 1974, [[0,0,0,2],[0,0,3,0],[0,7,0,0],[47,0,0,0]], [2,3,7,47], [[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]], [0,0,0,0], [3,2,1,0], "Fermat"⟩]

theorem n4_a5_entire_list : enumerate n4_a5_input = n4_a5_rows := by
  change enumerateCandidateEquations 4 5 = _
  rw [enumerateCandidateEquations, if_neg (by decide), Certificates.higher_4_5_entire_list]
  cbv

theorem n4_a5_payload : decodeClassificationPayload (classificationPayload n4_a5_input) =
    some (4,5,n4_a5_rows) := by
  rw [cli_payload_correct, n4_a5_entire_list]
  rfl

def n4_a25_input : Input := ⟨4,25,by decide,by decide⟩
def n4_a25_rows : List EquationData :=
  [⟨4, 25, [42,402,938,1407], 2814, [[0,0,0,2],[0,0,3,0],[0,7,0,0],[67,0,0,0]], [2,3,7,67], [[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]], [0,0,0,0], [3,2,1,0], "Fermat"⟩]

theorem n4_a25_entire_list : enumerate n4_a25_input = n4_a25_rows := by
  change enumerateCandidateEquations 4 25 = _
  rw [enumerateCandidateEquations, if_neg (by decide), Certificates.higher_4_25_entire_list]
  cbv

theorem n4_a25_payload : decodeClassificationPayload (classificationPayload n4_a25_input) =
    some (4,25,n4_a25_rows) := by
  rw [cli_payload_correct, n4_a25_entire_list]
  rfl

def n5_a1_input : Input := ⟨5,1,by decide,by decide⟩
def n5_a1_rows : List EquationData :=
  [⟨5, 1, [1806,75894,466206,1087814,1631721], 3263442, [[0,0,0,0,2],[0,0,0,3,0],[0,0,7,0,0],[0,43,0,0,0],[1807,0,0,0,0]], [2,3,7,43,1807], [[0,0,0,0,1],[0,0,0,1,0],[0,0,1,0,0],[0,1,0,0,0],[1,0,0,0,0]], [0,0,0,0,0], [4,3,2,1,0], "Fermat"⟩,
   ⟨5, 1, [1974,16590,111390,259910,389865], 779730, [[0,0,0,0,2],[0,0,0,3,0],[0,0,7,0,0],[0,47,0,0,0],[395,0,0,0,0]], [2,3,7,47,395], [[0,0,0,0,1],[0,0,0,1,0],[0,0,1,0,0],[0,1,0,0,0],[1,0,0,0,0]], [0,0,0,0,0], [4,3,2,1,0], "Fermat"⟩,
   ⟨5, 1, [1518,2046,4278,15686,23529], 47058, [[0,0,0,0,2],[0,0,0,3,0],[0,0,11,0,0],[0,23,0,0,0],[31,0,0,0,0]], [2,3,11,23,31], [[0,0,0,0,1],[0,0,0,1,0],[0,0,1,0,0],[0,1,0,0,0],[1,0,0,0,0]], [0,0,0,0,0], [4,3,2,1,0], "Fermat"⟩]

theorem n5_a1_entire_list : enumerate n5_a1_input = n5_a1_rows := by
  change enumerateCandidateEquations 5 1 = _
  rw [enumerateCandidateEquations, if_neg (by decide), Certificates.higher_5_1_entire_list]
  cbv

theorem n5_a1_payload : decodeClassificationPayload (classificationPayload n5_a1_input) =
    some (5,1,n5_a1_rows) := by
  rw [cli_payload_correct, n5_a1_entire_list]
  rfl

end CanonicalRoots.OutputCertificates
