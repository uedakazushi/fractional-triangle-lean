import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

noncomputable section
namespace CanonicalRoots

/-- A spanning family of a finite-dimensional vector space contains a basis of its exact dimension. -/
theorem finite_basis_selected_from_spanning {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ} (v : ι → V)
    (hv : Submodule.span K (Set.range v) = ⊤) (hn : Module.finrank K V = n) :
    ∃ f : Fin n → ι, Function.Injective f ∧
      ∃ b : Module.Basis (Fin n) K V, ∀ i, b i = v (f i) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  let b := Module.Basis.mk hli (by rw [hspan, hv])
  let : Finite κ := Module.Finite.finite_basis b
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = n := (Module.finrank_eq_card_basis b).symm.trans hn
  let e : κ ≃ Fin n := (Fintype.equivFin κ).trans (finCongr hc)
  refine ⟨fun i => a (e.symm i), ha.comp e.symm.injective, b.reindex e, ?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  exact Module.Basis.mk_apply hli _ (e.symm i)

end CanonicalRoots
