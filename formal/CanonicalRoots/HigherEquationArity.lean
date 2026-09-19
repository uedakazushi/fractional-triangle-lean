import CanonicalRoots.HigherEquationSemantics

noncomputable section
namespace CanonicalRoots

/-- Transport a Fermat presentation across an equality of the finite variable counts. -/
def fermatModelArityCast {n m : ℕ} (h : n = m) (p : Fin n → ℕ) :
    GradedAlgEquiv (presentedPiece (fermat p) (productWeights p))
      (presentedPiece (fermat (p ∘ (finCongr h).symm)) (productWeights (p ∘ (finCongr h).symm))) := by
  subst m
  exact { toAlgEquiv := AlgEquiv.refl
          preserves := fun _ _ => Iff.rfl }

def higherEquationOfFnModelEquiv {n : ℕ} (a : ℕ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) :
    GradedAlgEquiv (presentedPiece (fermat p) (productWeights p))
      (higherEquation a (List.ofFn p)).piece := by
  have hlen : n = (List.ofFn p).length := List.length_ofFn.symm
  have hg : p ∘ (finCongr hlen).symm = (List.ofFn p).get := by
    funext i
    simp [List.get_ofFn, finCongr]
    rfl
  have φ := fermatModelArityCast hlen p
  rw [hg] at φ
  exact φ.trans (higherEquationModelEquiv a (List.ofFn p) (by
    intro i
    rw [← hg]
    exact hp _))

end CanonicalRoots
