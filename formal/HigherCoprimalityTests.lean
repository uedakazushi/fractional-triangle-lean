import CanonicalRoots.HigherCoprimality

noncomputable section
open CanonicalRoots

-- The tail (4,5,7) is pairwise coprime, so the earlier tail theorem cannot reject this.
-- The full theorem detects the common factor of coordinates 0 and 1.
example : ¬ Nonempty (RootHypersurfacePresentation ![6, 4, 5, 7]
    (omegaDegree ![6, 4, 5, 7])) := by
  rintro ⟨H⟩
  let p : Fin 4 → ℕ := ![6, 4, 5, 7]
  have hp : AdmissibleSignature p := by
    constructor
    · intro k; fin_cases k <;> norm_num [p]
    · norm_num [p, Fin.sum_univ_succ]
  have h := H.pairwise_coprime p (omegaDegree p) hp (a := 1) (by decide)
    (by simp [IsCanonicalRoot]) (by decide) (i := (0 : Fin 4)) (j := 1) (by decide)
  norm_num [p, Nat.Coprime] at h

example {n a : ℕ} (t : Target (n + 1) a) (hn : 3 ≤ n) (i j : Fin (n + 1)) (hij : i ≠ j) :
    Nat.Coprime (t.signature i) (t.signature j) := t.pairwise_coprime hn hij

-- Coordinate transport preserves the canonical class even for a signature with torsion.
example : degreeReindex ![4, 6, 6, 5] (Equiv.swap 0 2)
    (omegaDegree (fun i => (![4, 6, 6, 5] : Fin 4 → ℕ) (Equiv.swap 0 2 i))) =
      omegaDegree ![4, 6, 6, 5] := degreeReindex_omega _ _

end
