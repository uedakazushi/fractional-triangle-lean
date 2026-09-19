import CanonicalRoots.RootReindex

noncomputable section
namespace CanonicalRoots

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
  {s : ℕ → Submodule ℂ A} {t : ℕ → Submodule ℂ B} {u : ℕ → Submodule ℂ C}

def GradedAlgEquiv.symm (e : GradedAlgEquiv s t) : GradedAlgEquiv t s where
  toAlgEquiv := e.toAlgEquiv.symm
  preserves m x := by
    simpa only [AlgEquiv.apply_symm_apply] using (e.preserves m (e.toAlgEquiv.symm x)).symm

def GradedAlgEquiv.trans (e : GradedAlgEquiv s t) (f : GradedAlgEquiv t u) : GradedAlgEquiv s u where
  toAlgEquiv := e.toAlgEquiv.trans f.toAlgEquiv
  preserves m x := (e.preserves m x).trans (f.preserves m (e.toAlgEquiv x))

/-- The already proved coordinate transport, packaged as an actual graded equivalence. -/
def rootGradedReindex {n : ℕ} (p : Fin n → ℕ) (e : Equiv.Perm (Fin n)) (τ : DegreeGroup p) :
    GradedAlgEquiv (rootPiece (fun i => p (e i)) ((degreeReindex p e).symm τ)) (rootPiece p τ) where
  toAlgEquiv := rootReindex p e τ
  preserves := rootReindex_preserves p e τ

end CanonicalRoots
