import CanonicalRoots.HigherTailCoprimality
import CanonicalRoots.TargetReindex

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
/-- Every pair of exponents of an actual isolated canonical-root hypersurface
in at least four ambient variables is coprime. -/
theorem RootHypersurfacePresentation.pairwise_coprime
    (H : RootHypersurfacePresentation p τ) (hn : 3 ≤ n) :
    Pairwise (fun i j => Nat.Coprime (p i) (p j)) := by
  classical
  intro i j hij
  have hex : ∃ k : Fin (n + 1), k ∉ ({i, j} : Finset (Fin (n + 1))) := by
    by_contra! he
    have hu : (Finset.univ : Finset (Fin (n + 1))) = {i, j} := by
      ext k
      simp only [Finset.mem_univ, true_iff]
      exact he k
    have hc := congrArg Finset.card hu
    simp [hij] at hc
    omega
  obtain ⟨k, hk⟩ := hex
  have hk' : k ≠ i ∧ k ≠ j := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
  let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 k
  have he0 : e 0 = k := Equiv.swap_apply_left 0 k
  have hiz : e.symm i ≠ 0 := by
    intro h
    have hh := congrArg e h
    rw [e.apply_symm_apply, he0] at hh
    exact hk'.1 hh.symm
  have hjz : e.symm j ≠ 0 := by
    intro h
    have hh := congrArg e h
    rw [e.apply_symm_apply, he0] at hh
    exact hk'.2 hh.symm
  obtain ⟨i', hi'⟩ := Fin.exists_succ_eq_of_ne_zero hiz
  obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero hjz
  have hij' : i' ≠ j' := by
    intro h
    apply hij
    apply e.symm.injective
    rw [← hi', ← hj', h]
  have hc := (H.reindex p e τ).tail_pairwise_coprime (fun l => p (e l))
    ((degreeReindex p e).symm τ) (admissibleSignature_reindex p e hp) ha
    (canonicalRoot_reindex p e τ hτ) hn hij'
  simpa only [hi', hj', e.apply_symm_apply] using hc

theorem Target.pairwise_coprime (t : Target (n + 1) a) (hn : 3 ≤ n) :
    Pairwise (fun i j => Nat.Coprime (t.signature i) (t.signature j)) :=
  t.presentation.pairwise_coprime t.signature t.tau t.admissible t.parameter_input t.root_equation hn

end CanonicalRoots
