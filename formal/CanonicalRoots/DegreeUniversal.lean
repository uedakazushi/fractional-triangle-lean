import CanonicalRoots.DegreeNormalForm

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} {G : Type*} [AddCommGroup G]

def freeDegreeEvaluation (xs : Fin n → G) (c : G) : FreeDegrees n →+ G where
  toFun u := u none • c + ∑ i, u (some i) • xs i
  map_zero' := by simp
  map_add' u v := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]; abel

@[simp] theorem freeDegreeEvaluation_c (xs : Fin n → G) (c : G) :
    freeDegreeEvaluation xs c (Pi.single none 1) = c := by
  simp [freeDegreeEvaluation]

@[simp] theorem freeDegreeEvaluation_x (xs : Fin n → G) (c : G) (i : Fin n) :
    freeDegreeEvaluation xs c (Pi.single (some i) 1) = xs i := by
  classical
  simp [freeDegreeEvaluation, Pi.single_apply, eq_comm]

/-- The universal map out of the original, unsaturated degree presentation. -/
def degreeLift (p : Fin n → ℕ) (xs : Fin n → G) (c : G)
    (hrel : ∀ i, (p i : ℤ) • xs i = c) : DegreeGroup p →+ G :=
  QuotientAddGroup.lift (degreeRelations p) (freeDegreeEvaluation xs c) (by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change freeDegreeEvaluation xs c _ = 0
    rw [map_sub, map_zsmul, freeDegreeEvaluation_x, freeDegreeEvaluation_c, hrel, sub_self])

@[simp] theorem degreeLift_c (p : Fin n → ℕ) (xs : Fin n → G) (c : G)
    (hrel : ∀ i, (p i : ℤ) • xs i = c) : degreeLift p xs c hrel (cDegree p) = c :=
  freeDegreeEvaluation_c xs c

@[simp] theorem degreeLift_x (p : Fin n → ℕ) (xs : Fin n → G) (c : G)
    (hrel : ∀ i, (p i : ℤ) • xs i = c) (i : Fin n) :
    degreeLift p xs c hrel (xDegree p i) = xs i := freeDegreeEvaluation_x xs c i

theorem degree_generators_span (p : Fin n → ℕ) (l : DegreeGroup p) :
    ∃ b : ℤ, ∃ v : Fin n → ℤ, l = b • cDegree p + ∑ i, v i • xDegree p i := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective (degreeRelations p) l
  refine ⟨u none, fun i => u (some i), ?_⟩
  rw [← normalDegree_expression]
  apply congrArg (QuotientAddGroup.mk' (degreeRelations p))
  funext k
  cases k <;> rfl

theorem degreeHom_ext (p : Fin n → ℕ) (f g : DegreeGroup p →+ G)
    (hc : f (cDegree p) = g (cDegree p)) (hx : ∀ i, f (xDegree p i) = g (xDegree p i)) : f = g := by
  apply AddMonoidHom.ext
  intro l
  obtain ⟨b, v, rfl⟩ := degree_generators_span p l
  simp only [map_add, map_zsmul, map_sum, hc, hx]

end CanonicalRoots
