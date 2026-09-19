import CanonicalRoots.AmbientReindex

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin n → ℕ) (e : Equiv.Perm (Fin n))
  (τ : DegreeGroup (fun i => p (e i)))

theorem rootModule_reindex_mem (z : AmbientRing (fun i => p (e i)))
    (hz : z ∈ rootModule (fun i => p (e i)) τ) :
    ambientReindex p e z ∈ rootModule p (degreeReindex p e τ) := by
  refine Submodule.iSup_induction (fun m : ℕ => ambientPiece (fun i => p (e i)) (m • τ))
    (motive := fun z => ambientReindex p e z ∈ rootModule p (degreeReindex p e τ)) hz
    (fun m z hz => ?_) ?_ (fun x y hx hy => ?_)
  · apply (le_iSup (fun m : ℕ => ambientPiece p (m • degreeReindex p e τ)) m)
    rw [← map_nsmul]
    exact (ambientPiece_reindex_iff p e (m • τ) z).mpr hz
  · simp only [map_zero, Submodule.zero_mem]
  · simpa only [map_add] using (rootModule p (degreeReindex p e τ)).add_mem hx hy

theorem rootModule_reindex_symm_mem (z : AmbientRing p)
    (hz : z ∈ rootModule p (degreeReindex p e τ)) :
    (ambientReindex p e).symm z ∈ rootModule (fun i => p (e i)) τ := by
  refine Submodule.iSup_induction (fun m : ℕ => ambientPiece p (m • degreeReindex p e τ))
    (motive := fun z => (ambientReindex p e).symm z ∈ rootModule (fun i => p (e i)) τ) hz
    (fun m z hz => ?_) ?_ (fun x y hx hy => ?_)
  · apply (le_iSup (fun m : ℕ => ambientPiece (fun i => p (e i)) (m • τ)) m)
    apply (ambientPiece_reindex_iff p e (m • τ) ((ambientReindex p e).symm z)).mp
    simpa only [AlgEquiv.apply_symm_apply, map_nsmul] using hz
  · simp only [map_zero, Submodule.zero_mem]
  · simpa only [map_add] using (rootModule (fun i => p (e i)) τ).add_mem hx hy

/-- Coordinate permutation restricts to an equivalence of the actual root subalgebras. -/
def rootReindexEquiv : RootRing (fun i => p (e i)) τ ≃ₐ[ℂ] RootRing p (degreeReindex p e τ) where
  toFun r := ⟨ambientReindex p e r, rootModule_reindex_mem p e τ r r.property⟩
  invFun r := ⟨(ambientReindex p e).symm r, rootModule_reindex_symm_mem p e τ r r.property⟩
  left_inv r := Subtype.ext ((ambientReindex p e).symm_apply_apply r)
  right_inv r := Subtype.ext ((ambientReindex p e).apply_symm_apply r)
  map_add' r s := Subtype.ext (map_add (ambientReindex p e) (r : AmbientRing (fun i => p (e i))) s)
  map_mul' r s := Subtype.ext (map_mul (ambientReindex p e) (r : AmbientRing (fun i => p (e i))) s)
  commutes' c := Subtype.ext ((ambientReindex p e).commutes c)

theorem rootReindexEquiv_preserves (m : ℕ) (r : RootRing (fun i => p (e i)) τ) :
    r ∈ rootPiece (fun i => p (e i)) τ m ↔
      rootReindexEquiv p e τ r ∈ rootPiece p (degreeReindex p e τ) m := by
  change (r : AmbientRing (fun i => p (e i))) ∈ ambientPiece (fun i => p (e i)) (m • τ) ↔
    ambientReindex p e r ∈ ambientPiece p (m • degreeReindex p e τ)
  rw [← map_nsmul]
  exact (ambientPiece_reindex_iff p e (m • τ) r).symm

/-- The variant whose target uses the initially specified root. -/
def rootReindex (ρ : DegreeGroup p) :
    RootRing (fun i => p (e i)) ((degreeReindex p e).symm ρ) ≃ₐ[ℂ] RootRing p ρ where
  toFun r := ⟨ambientReindex p e r, by
    change ambientReindex p e (r : AmbientRing (fun i => p (e i))) ∈ rootModule p ρ
    simpa only [AddEquiv.apply_symm_apply] using
      rootModule_reindex_mem p e ((degreeReindex p e).symm ρ) r r.property⟩
  invFun r := ⟨(ambientReindex p e).symm r, rootModule_reindex_symm_mem p e
    ((degreeReindex p e).symm ρ) r (by
      simpa only [AddEquiv.apply_symm_apply] using (show (r : AmbientRing p) ∈ rootModule p ρ from r.property))⟩
  left_inv r := Subtype.ext ((ambientReindex p e).symm_apply_apply r)
  right_inv r := Subtype.ext ((ambientReindex p e).apply_symm_apply r)
  map_add' r s := Subtype.ext (map_add (ambientReindex p e) (r : AmbientRing (fun i => p (e i))) s)
  map_mul' r s := Subtype.ext (map_mul (ambientReindex p e) (r : AmbientRing (fun i => p (e i))) s)
  commutes' c := Subtype.ext ((ambientReindex p e).commutes c)

theorem rootReindex_preserves (ρ : DegreeGroup p) (m : ℕ)
    (r : RootRing (fun i => p (e i)) ((degreeReindex p e).symm ρ)) :
    r ∈ rootPiece (fun i => p (e i)) ((degreeReindex p e).symm ρ) m ↔
      rootReindex p e ρ r ∈ rootPiece p ρ m := by
  change (r : AmbientRing (fun i => p (e i))) ∈
    ambientPiece (fun i => p (e i)) (m • (degreeReindex p e).symm ρ) ↔
      ambientReindex p e r ∈ ambientPiece p (m • ρ)
  simpa only [map_nsmul, AddEquiv.apply_symm_apply] using
    (ambientPiece_reindex_iff p e (m • (degreeReindex p e).symm ρ) r).symm

end CanonicalRoots
