import CanonicalRoots.HigherTailCoprimality

noncomputable section
open CanonicalRoots

-- This excludes an actual graded isolated hypersurface presentation of the root ring.
-- It does not merely reject a numerical candidate or an assumed cyclic model.
example : ¬ Nonempty (RootHypersurfacePresentation ![4, 6, 6, 5]
    (omegaDegree ![4, 6, 6, 5])) := by
  rintro ⟨H⟩
  let p : Fin 4 → ℕ := ![4, 6, 6, 5]
  have hp : AdmissibleSignature p := by
    constructor
    · intro k; fin_cases k <;> norm_num [p]
    · norm_num [p, Fin.sum_univ_succ]
  have h := H.tail_pairwise_coprime p (omegaDegree p) hp (a := 1) (by decide)
    (by simp [IsCanonicalRoot]) (by decide) (i := (0 : Fin 3)) (j := 1) (by decide)
  norm_num [p, Nat.Coprime] at h

-- The conclusion retains torsion in the original degree group and quantifies actual targets.
example {n a : ℕ} (t : Target (n + 1) a) (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    Nat.Coprime (t.signature i.succ) (t.signature j.succ) :=
  t.tail_pairwise_coprime hn hij

end
