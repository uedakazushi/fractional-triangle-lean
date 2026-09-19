import CanonicalRoots.RootMonomialBasis

noncomputable section
namespace CanonicalRoots

/-- Regroup a scalar basis into a basis over a larger algebra, once the scalar action
has been identified on every basis vector. -/
theorem regroup_linearCombination_bijective
    {P M D I : Type*} [CommRing P] [Algebra ℂ P] [AddCommGroup M]
    [Module P M] [Module ℂ M] [IsScalarTower ℂ P M]
    (w : Module.Basis D ℂ P) (b : Module.Basis (D × I) ℂ M) (v : I → M)
    (h : ∀ d i, w d • v i = b (d, i)) :
    Function.Bijective (Finsupp.linearCombination P v) := by
  let b' := b.reindex (Equiv.prodComm D I)
  have hb : (fun q : I × D => w q.2 • v q.1) = b' := by
    funext q
    rcases q with ⟨i, d⟩
    simpa [b', Module.Basis.reindex_apply] using h d i
  have hbij : Function.Bijective
      (Finsupp.linearCombination ℂ (fun q : I × D => w q.2 • v q.1)) := by
    rw [hb, ← b'.coe_repr_symm]
    exact b'.repr.symm.bijective
  rw [Finsupp.linearCombination_smul] at hbij
  have he : Function.Bijective
      ((Finsupp.mapRange.linearMap (Finsupp.linearCombination ℂ w)).comp
        (Finsupp.curryLinearEquiv ℂ).toLinearMap :
          (I × D →₀ ℂ) →ₗ[ℂ] (I →₀ P)) := by
    rw [← w.coe_repr_symm, ← Finsupp.mapRange.linearEquiv_toLinearMap]
    exact (Finsupp.mapRange.linearEquiv w.repr.symm).bijective.comp
      (Finsupp.curryLinearEquiv ℂ).bijective
  exact (Function.Bijective.of_comp_iff (Finsupp.linearCombination P v) he).mp hbij

def regroupBasis
    {P M D I : Type*} [CommRing P] [Algebra ℂ P] [AddCommGroup M]
    [Module P M] [Module ℂ M] [IsScalarTower ℂ P M]
    (w : Module.Basis D ℂ P) (b : Module.Basis (D × I) ℂ M) (v : I → M)
    (h : ∀ d i, w d • v i = b (d, i)) : Module.Basis I P M :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination P v)
    (regroup_linearCombination_bijective w b v h)).symm

@[simp] theorem regroupBasis_apply
    {P M D I : Type*} [CommRing P] [Algebra ℂ P] [AddCommGroup M]
    [Module P M] [Module ℂ M] [IsScalarTower ℂ P M]
    (w : Module.Basis D ℂ P) (b : Module.Basis (D × I) ℂ M) (v : I → M)
    (h : ∀ d i, w d • v i = b (d, i)) (i : I) : regroupBasis w b v h i = v i := by
  change Finsupp.linearCombination P v (Finsupp.single i 1) = v i
  simp

end CanonicalRoots
