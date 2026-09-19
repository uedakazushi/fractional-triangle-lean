import CanonicalRoots.TernaryRootSignatureInvariant
import CanonicalRoots.GradedEquivComposition
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
namespace CanonicalRoots

theorem signature_permutation_of_multiset_eq {n : ℕ} (p q : Fin n → ℕ)
    (h : (List.ofFn p : Multiset ℕ) = (List.ofFn q : Multiset ℕ)) :
    ∃ σ : Equiv.Perm (Fin n), p = q ∘ σ := by
  have hperm : List.Perm (List.ofFn p) (List.ofFn q) := Multiset.coe_eq_coe.mp h
  have hs : p ∘ Tuple.sort p = q ∘ Tuple.sort q := by
    apply List.ofFn_injective
    exact (((Tuple.sort p).ofFn_comp_perm p).trans
      (hperm.trans ((Tuple.sort q).ofFn_comp_perm q).symm)).eq_of_pairwise'
      (Tuple.monotone_sort p).sortedLE_ofFn.pairwise (Tuple.monotone_sort q).sortedLE_ofFn.pairwise
  refine ⟨(Tuple.sort p).symm.trans (Tuple.sort q), funext fun i => ?_⟩
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.trans_apply] using
    congrFun hs ((Tuple.sort p).symm i)

theorem root_gradedEquiv_of_signature_multiset_eq {n a : ℕ} (p q : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (ha : 1 ≤ a) (τ : DegreeGroup p) (υ : DegreeGroup q)
    (hτ : IsCanonicalRoot p a τ) (hυ : IsCanonicalRoot q a υ)
    (h : (List.ofFn p : Multiset ℕ) = (List.ofFn q : Multiset ℕ)) :
    Nonempty (GradedAlgEquiv (rootPiece p τ) (rootPiece q υ)) := by
  obtain ⟨σ, hσ⟩ := signature_permutation_of_multiset_eq p q h
  subst p
  have he : τ = (degreeReindex q σ).symm υ :=
    canonicalRoot_unique (q ∘ σ) hp ha τ _ hτ (canonicalRoot_reindex q σ υ hυ)
  subst τ
  exact ⟨rootGradedReindex q σ υ⟩

/-- At a fixed positive root index, actual ternary canonical-root rings are
graded-isomorphic exactly when their original signatures agree as multisets. -/
theorem ternary_root_gradedEquiv_iff_signature {a : ℕ} (p q : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (hq : AdmissibleSignature q) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (υ : DegreeGroup q) (hτ : IsCanonicalRoot p a τ) (hυ : IsCanonicalRoot q a υ) :
    Nonempty (GradedAlgEquiv (rootPiece p τ) (rootPiece q υ)) ↔
      (List.ofFn p : Multiset ℕ) = (List.ofFn q : Multiset ℕ) := by
  constructor
  · rintro ⟨e⟩
    exact ternary_root_gradedEquiv_signature_eq p q hp hq ha τ υ hτ hυ e
  · exact root_gradedEquiv_of_signature_multiset_eq p q
      (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) ha τ υ hτ hυ

end CanonicalRoots
