import CanonicalRoots.AmbientBasis
import CanonicalRoots.AmbientGrading

noncomputable section
namespace CanonicalRoots

/-- The indices of the quotient monomial basis in one actual group degree. -/
def AmbientPieceIndex {n : ℕ} (p : Fin (n + 1) → ℕ) (l : DegreeGroup p) :=
  {q : (Fin n →₀ ℕ) × Fin (p 0) //
    Finsupp.weight (xDegree p) (q.1.cons (q.2 : ℕ)) = l}

theorem ambientPiece_eq_span {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (l : DegreeGroup p) :
    ambientPiece p l = Submodule.span ℂ
      (Set.range (fun q : AmbientPieceIndex p l => ambientMonomialBasis p hp q.val)) := by
  classical
  apply le_antisymm
  · intro x hx
    have hrepr := (ambientMonomialBasis p hp).linearCombination_repr x
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
    have hproject := congrArg (ambientProjection p l) hrepr
    rw [ambientProjection_eq_self p l hx, map_sum] at hproject
    rw [← hproject]
    apply Submodule.sum_mem
    intro q hq
    rw [map_smul, ambientProjection_of_mem p l _ (ambientMonomialBasis_homogeneous p hp q)]
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨q, h.symm⟩, rfl⟩)
    · simp
  · apply Submodule.span_le.mpr
    rintro x ⟨q, rfl⟩
    have h := ambientMonomialBasis_homogeneous p hp q.val
    rw [q.property] at h
    exact h

/-- Restriction of the proven quotient basis, not a formal space with prescribed dimensions. -/
def ambientPieceBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (l : DegreeGroup p) : Module.Basis (AmbientPieceIndex p l) ℂ (ambientPiece p l) :=
  (Module.Basis.span ((ambientMonomialBasis p hp).linearIndependent.comp
    (fun q : AmbientPieceIndex p l => q.val) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (ambientPiece_eq_span p hp l).symm)

@[simp] theorem ambientPieceBasis_apply {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (l : DegreeGroup p) (q : AmbientPieceIndex p l) :
    (ambientPieceBasis p hp l q : AmbientRing p) = ambientMonomialBasis p hp q.val := by
  simp only [ambientPieceBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply, Function.comp_apply]

/-- Each root-degree piece is exactly its ambient degree piece as a vector space. -/
def rootPieceEquivAmbient {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (m : ℕ) :
    rootPiece p τ m ≃ₗ[ℂ] ambientPiece p (m • τ) where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, (le_iSup (fun k : ℕ => ambientPiece p (k • τ)) m) x.property⟩,
    x.property⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_add' _x _y := rfl
  map_smul' _r _x := rfl

def rootPieceBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (τ : DegreeGroup p) (m : ℕ) :
    Module.Basis (AmbientPieceIndex p (m • τ)) ℂ (rootPiece p τ m) :=
  (ambientPieceBasis p hp (m • τ)).map (rootPieceEquivAmbient p τ m).symm

end CanonicalRoots
