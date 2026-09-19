import CanonicalRoots.CandidateData
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace CanonicalRoots

def candidateDedupStep (acc : List TernaryCandidate) (e : TernaryCandidate) : List TernaryCandidate :=
  if acc.any (fun f => candidateKey f == candidateKey e) then acc else acc ++ [e]

theorem candidateDedupStep_mem {acc : List TernaryCandidate} {e f : TernaryCandidate}
    (hf : f ∈ candidateDedupStep acc e) : f ∈ acc ∨ f = e := by
  unfold candidateDedupStep at hf
  split_ifs at hf <;> simp_all

theorem candidateDedupStep_keys (acc : List TernaryCandidate) (e : TernaryCandidate) (k : List ℤ) :
    k ∈ (candidateDedupStep acc e).map candidateKey ↔ k ∈ acc.map candidateKey ∨ k = candidateKey e := by
  unfold candidateDedupStep
  split_ifs with h
  · have he : candidateKey e ∈ acc.map candidateKey := by
      obtain ⟨f,hf,hkey⟩ := List.any_eq_true.mp h
      exact List.mem_map.mpr ⟨f,hf,by simpa using hkey⟩
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact he
  · simp

theorem candidateDedupStep_nodup (acc : List TernaryCandidate) (e : TernaryCandidate)
    (hacc : (acc.map candidateKey).Nodup) : ((candidateDedupStep acc e).map candidateKey).Nodup := by
  unfold candidateDedupStep
  split_ifs with h
  · exact hacc
  · have hn : candidateKey e ∉ acc.map candidateKey := by
      intro he
      obtain ⟨f,hf,hkey⟩ := List.mem_map.mp he
      exact h (List.any_eq_true.mpr ⟨f,hf,by simpa using hkey⟩)
    simpa using (List.nodup_append.mpr ⟨hacc,by simp,by simpa using hn⟩)

theorem candidateDedupFold_mem (es acc : List TernaryCandidate) (f : TernaryCandidate)
    (hf : f ∈ es.foldl candidateDedupStep acc) : f ∈ acc ∨ f ∈ es := by
  induction es generalizing acc with
  | nil => exact Or.inl hf
  | cons e es ih =>
    rcases ih (candidateDedupStep acc e) hf with h | h
    · rcases candidateDedupStep_mem h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem candidateDedupFold_keys (es acc : List TernaryCandidate) (k : List ℤ) :
    k ∈ (es.foldl candidateDedupStep acc).map candidateKey ↔
      k ∈ acc.map candidateKey ∨ k ∈ es.map candidateKey := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, candidateDedupStep_keys]
    simp only [List.map_cons, List.mem_cons]
    tauto

theorem candidateDedupFold_nodup (es acc : List TernaryCandidate)
    (hacc : (acc.map candidateKey).Nodup) : (es.foldl candidateDedupStep acc |>.map candidateKey).Nodup := by
  induction es generalizing acc with
  | nil => exact hacc
  | cons e es ih => exact ih _ (candidateDedupStep_nodup acc e hacc)

theorem dedupCandidates_mem {es : List TernaryCandidate} {e : TernaryCandidate}
    (he : e ∈ dedupCandidates es) : e ∈ es := by
  exact (candidateDedupFold_mem es [] e he).resolve_left (by simp)

theorem dedupCandidates_keys (es : List TernaryCandidate) (k : List ℤ) :
    k ∈ (dedupCandidates es).map candidateKey ↔ k ∈ es.map candidateKey := by
  change k ∈ (es.foldl candidateDedupStep []).map candidateKey ↔ k ∈ es.map candidateKey
  simpa only [List.map_nil, List.not_mem_nil, false_or] using candidateDedupFold_keys es [] k

theorem dedupCandidates_key_coverage {es : List TernaryCandidate} {e : TernaryCandidate}
    (he : e ∈ es) : ∃ f ∈ dedupCandidates es, candidateKey f = candidateKey e := by
  apply List.mem_map.mp
  exact (dedupCandidates_keys es _).mpr (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem dedupCandidates_keys_nodup (es : List TernaryCandidate) :
    ((dedupCandidates es).map candidateKey).Nodup :=
  candidateDedupFold_nodup es [] (by simp)

end CanonicalRoots
