import CanonicalRoots.HigherConverse
import CanonicalRoots.HigherSignatureList
import CanonicalRoots.GradedEquivComposition

noncomputable section
namespace CanonicalRoots

theorem signature_injective_of_coprime {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i)
    (hc : Pairwise (fun i j => Nat.Coprime (p i) (p j))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hone := Nat.eq_one_of_dvd_coprimes (hc hij) (dvd_refl (p i)) (by rw [he])
  have := hp i
  omega

theorem strictMono_signature_sort {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i)
    (hc : Pairwise (fun i j => Nat.Coprime (p i) (p j))) :
    StrictMono (fun i => p (Tuple.sort p i)) :=
  (Tuple.monotone_sort p).strictMono_of_injective
    ((signature_injective_of_coprime p hp hc).comp (Tuple.sort p).injective)

/-- Sorted rows of the actual arithmetic enumerator are exactly signatures of
actual higher-dimensional Targets. No positivity hypothesis is imposed on the input tuple. -/
theorem higher_sorted_signature_enumerated_iff {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hn : 3 ≤ n) (ha : 1 ≤ a) :
    List.ofFn p ∈ enumerateHigherCandidates (n + 1) a ↔
      StrictMono p ∧ ∃ t : Target (n + 1) a, t.signature = p := by
  constructor
  · intro hm
    have hA := (enumerateHigherCandidates_iff (n + 1) a ha (List.ofFn p)).mp hm
    have hp : ∀ i, 2 ≤ p i := fun i => hA.2.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨_, hs, hc, hd⟩ := (enumerateHigherCandidates_ofFn_iff p
      (fun i => lt_of_lt_of_le (by decide) (hp i)) ha).mp hm
    exact ⟨hs, (higher_signature_target_iff p hn hp ha).mpr ⟨hc, hd⟩⟩
  · rintro ⟨hs, t, rfl⟩
    apply (enumerateHigherCandidates_ofFn_iff t.signature
      (fun i => lt_of_lt_of_le (by decide) (t.admissible.1 i)) ha).mpr
    exact ⟨t.admissible.1, hs, t.pairwise_coprime hn, t.higher_product_defect hn⟩

theorem enumerateHigherCandidates_target_sound {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (ps : List ℕ) (hm : ps ∈ enumerateHigherCandidates (n + 1) a) :
    ∃ t : Target (n + 1) a, List.ofFn t.signature = ps := by
  obtain ⟨m, p, hp⟩ : ∃ m, ∃ p : Fin m → ℕ, ps = List.ofFn p :=
    ⟨ps.length, ps.get, (List.ofFn_get ps).symm⟩
  subst ps
  have hlen : m = n + 1 := by
    simpa only [List.length_ofFn] using ((enumerateHigherCandidates_iff (n + 1) a ha _).mp hm).1
  subst m
  obtain ⟨_, t, ht⟩ := (higher_sorted_signature_enumerated_iff p hn ha).mp hm
  exact ⟨t, congrArg List.ofFn ht⟩

theorem Target.higher_sorted_signature_enumerated {n a : ℕ} (t : Target (n + 1) a) (hn : 3 ≤ n) :
    List.ofFn (fun i => t.signature (Tuple.sort t.signature i)) ∈ enumerateHigherCandidates (n + 1) a := by
  apply (higher_sorted_signature_enumerated_iff _ hn t.parameter_input).mpr
  exact ⟨strictMono_signature_sort t.signature t.admissible.1 (t.pairwise_coprime hn),
    t.reindex (Tuple.sort t.signature), rfl⟩

/-- Every actual higher-dimensional target is graded-isomorphic to a Fermat model
whose signature occurs in the finite enumerator. -/
theorem Target.higher_enumerated_graded_model {n a : ℕ} (t : Target (n + 1) a) (hn : 3 ≤ n) :
    ∃ p : Fin (n + 1) → ℕ, List.ofFn p ∈ enumerateHigherCandidates (n + 1) a ∧
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
        (presentedPiece (fermat p) (productWeights p))) := by
  let e := Tuple.sort t.signature
  let s := t.reindex e
  refine ⟨s.signature, t.higher_sorted_signature_enumerated hn, ?_⟩
  let E := higherRootGradedEquiv s.signature s.admissible.1 s.parameter_input
    (s.pairwise_coprime hn) (s.higher_product_defect hn) s.tau s.root_equation
  exact ⟨(rootGradedReindex t.signature e t.tau).symm.trans E⟩

end CanonicalRoots
