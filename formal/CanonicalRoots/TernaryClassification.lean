import CanonicalRoots.CandidateKeySemantics
import CanonicalRoots.CandidateDedup

noncomputable section
namespace CanonicalRoots

def ternaryRepresentative (a : ℕ)
    (i : Fin (dedupCandidates (enumerateTernaryCandidates a)).length) : TernaryCandidate :=
  (dedupCandidates (enumerateTernaryCandidates a)).get i

theorem ternaryRepresentative_arithmetic {a : ℕ} (ha : 1 ≤ a)
    (i : Fin (dedupCandidates (enumerateTernaryCandidates a)).length) :
    ArithmeticTernary a (ternaryRepresentative a i) :=
  (enumerateTernaryCandidates_iff a ha _).mp (dedupCandidates_mem (List.get_mem _ i))

theorem ternary_representatives_sound {a : ℕ} (ha : 1 ≤ a)
    (i : Fin (dedupCandidates (enumerateTernaryCandidates a)).length) :
    ∃ t : Target 3 a, t.signature = candidateSignature (ternaryRepresentative a i) ∧
      Nonempty (GradedAlgEquiv
        (presentedPiece (candidateRelation (ternaryRepresentative a i))
          (candidateNatWeights (ternaryRepresentative a i))) (rootPiece t.signature t.tau)) :=
  ⟨candidateTarget ha (ternaryRepresentative_arithmetic ha i),
    candidateTarget_signature ha _,⟨candidateTargetGradedEquiv ha _⟩⟩

theorem ternary_representatives_pairwise_nonisomorphic {a : ℕ} (ha : 1 ≤ a)
    (i j : Fin (dedupCandidates (enumerateTernaryCandidates a)).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv
      (presentedPiece (candidateRelation (ternaryRepresentative a i))
        (candidateNatWeights (ternaryRepresentative a i)))
      (presentedPiece (candidateRelation (ternaryRepresentative a j))
        (candidateNatWeights (ternaryRepresentative a j)))) := by
  intro hφ
  have hkey := (candidateKey_eq_iff_gradedEquiv ha (ternaryRepresentative_arithmetic ha i)
    (ternaryRepresentative_arithmetic ha j)).mpr hφ
  have hn := dedupCandidates_keys_nodup (enumerateTernaryCandidates a)
  let ii : Fin ((dedupCandidates (enumerateTernaryCandidates a)).map candidateKey).length :=
    ⟨i.val,by simpa using i.isLt⟩
  let jj : Fin ((dedupCandidates (enumerateTernaryCandidates a)).map candidateKey).length :=
    ⟨j.val,by simpa using j.isLt⟩
  have he : ii = jj := hn.injective_get (by simpa [ii,jj,ternaryRepresentative] using hkey)
  have hv : ii.val = jj.val := congrArg Fin.val he
  exact hij (Fin.ext hv)

/-- Each arbitrary actual ternary target has exactly one isomorphic retained output position. -/
theorem Target.ternary_representatives_complete_unique {a : ℕ} (t : Target 3 a) :
    ∃! i : Fin (dedupCandidates (enumerateTernaryCandidates a)).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (candidateRelation (ternaryRepresentative a i))
          (candidateNatWeights (ternaryRepresentative a i)))) := by
  obtain ⟨e,he,⟨φ⟩⟩ := t.ternary_enumerated_model
  obtain ⟨f,hf,hkey⟩ := dedupCandidates_key_coverage he
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hf
  have hei : ternaryRepresentative a i = f := hi
  have hfe := (candidateKey_eq_iff_gradedEquiv t.parameter_input
    ((enumerateTernaryCandidates_iff a t.parameter_input _).mp (dedupCandidates_mem hf))
    ((enumerateTernaryCandidates_iff a t.parameter_input _).mp he)).mp hkey
  obtain ⟨ψ⟩ := hfe
  have hmodel : Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
      (presentedPiece (candidateRelation (ternaryRepresentative a i))
        (candidateNatWeights (ternaryRepresentative a i)))) := by
    rw [hei]
    exact ⟨φ.trans ψ.symm⟩
  refine ⟨i,hmodel,?_⟩
  rintro j ⟨χ⟩
  by_contra hji
  obtain ⟨η⟩ := hmodel
  exact ternary_representatives_pairwise_nonisomorphic t.parameter_input j i hji
    ⟨χ.symm.trans η⟩

end CanonicalRoots
