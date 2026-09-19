import CanonicalRoots.HigherModelNonisomorphism
import CanonicalRoots.HigherEnumerationNodup

noncomputable section
namespace CanonicalRoots

def signatureOfList (ps : List ℕ) {n : ℕ} (hlen : ps.length = n) : Fin n → ℕ :=
  fun i => ps.get ⟨i.val, by omega⟩

theorem ofFn_signatureOfList (ps : List ℕ) {n : ℕ} (hlen : ps.length = n) :
    List.ofFn (signatureOfList ps hlen) = ps := by
  subst n
  change List.ofFn ps.get = ps
  exact List.ofFn_get ps

/-- The signature stored at an actual position of the executable higher list. -/
def higherCandidateSignature (n a : ℕ) (ha : 1 ≤ a)
    (i : Fin (enumerateHigherCandidates n a).length) : Fin n → ℕ :=
  signatureOfList ((enumerateHigherCandidates n a).get i)
    (((enumerateHigherCandidates_iff n a ha _).mp (List.get_mem _ i)).1)

theorem ofFn_higherCandidateSignature (n a : ℕ) (ha : 1 ≤ a)
    (i : Fin (enumerateHigherCandidates n a).length) :
    List.ofFn (higherCandidateSignature n a ha i) = (enumerateHigherCandidates n a).get i :=
  ofFn_signatureOfList _ _

/-- Nonisomorphism refers to different output positions, not only different keys. -/
theorem higher_candidates_pairwise_nonisomorphic {n a : ℕ} (ha : 1 ≤ a)
    (i j : Fin (enumerateHigherCandidates n a).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv
      (presentedPiece (fermat (higherCandidateSignature n a ha i))
        (productWeights (higherCandidateSignature n a ha i)))
      (presentedPiece (fermat (higherCandidateSignature n a ha j))
        (productWeights (higherCandidateSignature n a ha j)))) := by
  apply enumerateHigherCandidates_models_nonisomorphic ha
  · rw [ofFn_higherCandidateSignature]
    exact List.get_mem _ i
  · rw [ofFn_higherCandidateSignature]
    exact List.get_mem _ j
  · intro he
    apply hij
    apply (enumerateHigherCandidates_nodup n a).injective_get
    rw [← ofFn_higherCandidateSignature n a ha i,
      ← ofFn_higherCandidateSignature n a ha j, he]

theorem higher_candidates_sound {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (i : Fin (enumerateHigherCandidates (n + 1) a).length) :
    ∃ t : Target (n + 1) a, t.signature = higherCandidateSignature (n + 1) a ha i ∧
      Nonempty (GradedAlgEquiv
        (presentedPiece (fermat (higherCandidateSignature (n + 1) a ha i))
          (productWeights (higherCandidateSignature (n + 1) a ha i)))
        (rootPiece t.signature t.tau)) := by
  have hm : List.ofFn (higherCandidateSignature (n + 1) a ha i) ∈
      enumerateHigherCandidates (n + 1) a := by
    rw [ofFn_higherCandidateSignature]
    exact List.get_mem _ i
  obtain ⟨_, t, ht⟩ := (higher_sorted_signature_enumerated_iff _ hn ha).mp hm
  refine ⟨t, ht, ?_⟩
  rw [← ht]
  exact ⟨(higherRootGradedEquiv t.signature t.admissible.1 ha (t.pairwise_coprime hn)
    (t.higher_product_defect hn) t.tau t.root_equation).symm⟩

/-- Every actual target has exactly one graded-isomorphic output position. -/
theorem Target.higher_candidates_complete_unique {n a : ℕ} (t : Target (n + 1) a)
    (hn : 3 ≤ n) :
    ∃! i : Fin (enumerateHigherCandidates (n + 1) a).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (fermat (higherCandidateSignature (n + 1) a t.parameter_input i))
          (productWeights (higherCandidateSignature (n + 1) a t.parameter_input i)))) := by
  obtain ⟨p, hp, he⟩ := t.higher_enumerated_graded_model hn
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  have hpi : higherCandidateSignature (n + 1) a t.parameter_input i = p := by
    apply List.ofFn_injective
    rw [ofFn_higherCandidateSignature, hi]
  have hei : Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
      (presentedPiece (fermat (higherCandidateSignature (n + 1) a t.parameter_input i))
        (productWeights (higherCandidateSignature (n + 1) a t.parameter_input i)))) := by
    rwa [hpi]
  refine ⟨i, hei, ?_⟩
  rintro j ⟨ej⟩
  by_contra hji
  obtain ⟨ei⟩ := hei
  exact higher_candidates_pairwise_nonisomorphic t.parameter_input j i hji
    ⟨ej.symm.trans ei⟩

end CanonicalRoots
