import CanonicalRoots.Candidates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CanonicalRoots.Certificates

def explicitTernary1 : List TernaryCandidate :=
  [⟨.I, 2, 3, 7⟩,
   ⟨.II, 2, 2, 5⟩,
   ⟨.II, 2, 4, 3⟩,
   ⟨.II, 3, 5, 2⟩,
   ⟨.II, 4, 2, 3⟩,
   ⟨.II, 5, 3, 2⟩,
   ⟨.III, 2, 2, 4⟩,
   ⟨.III, 2, 3, 3⟩,
   ⟨.III, 3, 4, 2⟩,
   ⟨.IV, 2, 2, 4⟩,
   ⟨.IV, 2, 3, 3⟩,
   ⟨.IV, 3, 3, 2⟩,
   ⟨.IV, 4, 2, 2⟩,
   ⟨.V, 2, 2, 3⟩]
theorem ternary_1_entire_list :
    dedupCandidates (enumerateTernaryCandidates 1) = explicitTernary1 := by
  unfold dedupCandidates candidateKey
  simp only [List.mergeSort_eq_insertionSort]
  decide +kernel

def explicitTernary2 : List TernaryCandidate :=
  [⟨.II, 5, 2, 3⟩,
   ⟨.III, 2, 2, 5⟩,
   ⟨.III, 2, 4, 3⟩,
   ⟨.IV, 3, 4, 2⟩,
   ⟨.IV, 5, 2, 2⟩,
   ⟨.V, 2, 2, 4⟩]
theorem ternary_2_entire_list :
    dedupCandidates (enumerateTernaryCandidates 2) = explicitTernary2 := by
  unfold dedupCandidates candidateKey
  simp only [List.mergeSort_eq_insertionSort]
  decide +kernel

def explicitTernary3 : List TernaryCandidate :=
  [⟨.II, 2, 2, 7⟩,
   ⟨.II, 7, 3, 2⟩,
   ⟨.III, 2, 3, 4⟩,
   ⟨.III, 3, 6, 2⟩,
   ⟨.IV, 2, 2, 6⟩,
   ⟨.IV, 2, 5, 3⟩,
   ⟨.IV, 4, 3, 2⟩,
   ⟨.V, 2, 3, 3⟩]
theorem ternary_3_entire_list :
    dedupCandidates (enumerateTernaryCandidates 3) = explicitTernary3 := by
  unfold dedupCandidates candidateKey
  simp only [List.mergeSort_eq_insertionSort]
  decide +kernel

def explicitTernary4 : List TernaryCandidate :=
  [⟨.II, 3, 2, 5⟩,
   ⟨.II, 7, 2, 3⟩,
   ⟨.III, 2, 2, 7⟩,
   ⟨.III, 2, 6, 3⟩,
   ⟨.IV, 3, 2, 4⟩,
   ⟨.IV, 3, 6, 2⟩,
   ⟨.IV, 7, 2, 2⟩,
   ⟨.V, 2, 2, 6⟩]
theorem ternary_4_entire_list :
    dedupCandidates (enumerateTernaryCandidates 4) = explicitTernary4 := by
  unfold dedupCandidates candidateKey
  simp only [List.mergeSort_eq_insertionSort]
  decide +kernel

def explicitTernary5 : List TernaryCandidate :=
  [⟨.I, 2, 3, 11⟩,
   ⟨.II, 2, 2, 9⟩,
   ⟨.II, 2, 8, 3⟩,
   ⟨.II, 3, 9, 2⟩,
   ⟨.II, 8, 2, 3⟩,
   ⟨.II, 9, 3, 2⟩,
   ⟨.III, 2, 2, 8⟩,
   ⟨.III, 2, 4, 4⟩,
   ⟨.III, 2, 7, 3⟩,
   ⟨.III, 3, 8, 2⟩,
   ⟨.III, 4, 5, 2⟩,
   ⟨.IV, 2, 2, 8⟩,
   ⟨.IV, 2, 3, 5⟩,
   ⟨.IV, 2, 4, 4⟩,
   ⟨.IV, 2, 7, 3⟩,
   ⟨.IV, 3, 3, 3⟩,
   ⟨.IV, 3, 7, 2⟩,
   ⟨.IV, 4, 4, 2⟩,
   ⟨.IV, 8, 2, 2⟩,
   ⟨.V, 2, 2, 7⟩,
   ⟨.V, 2, 3, 4⟩]
theorem ternary_5_entire_list :
    dedupCandidates (enumerateTernaryCandidates 5) = explicitTernary5 := by
  unfold dedupCandidates candidateKey
  simp only [List.mergeSort_eq_insertionSort]
  decide +kernel

def explicitTernary6 : List TernaryCandidate :=
  []
theorem ternary_6_entire_list :
    dedupCandidates (enumerateTernaryCandidates 6) = explicitTernary6 := by
  unfold dedupCandidates candidateKey
  simp only [List.mergeSort_eq_insertionSort]
  decide +kernel

theorem higher_4_1_entire_list :
    enumerateHigherCandidates 4 1 = [[2, 3, 7, 43]] := by
  decide +kernel

theorem higher_4_5_entire_list :
    enumerateHigherCandidates 4 5 = [[2, 3, 7, 47]] := by
  decide +kernel

theorem higher_4_25_entire_list :
    enumerateHigherCandidates 4 25 = [[2, 3, 7, 67]] := by
  decide +kernel

theorem higher_5_1_entire_list :
    enumerateHigherCandidates 5 1 = [[2, 3, 7, 43, 1807], [2, 3, 7, 47, 395], [2, 3, 11, 23, 31]] := by
  decide +kernel

end CanonicalRoots.Certificates
