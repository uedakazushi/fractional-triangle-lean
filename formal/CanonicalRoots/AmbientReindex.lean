import CanonicalRoots.DegreeReindex

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (p : Fin n → ℕ) (e : Equiv.Perm (Fin n))

theorem rename_fermat_reindex :
    rename e (fermat (fun i => p (e i))) = fermat p := by
  simp only [fermat, map_sum, map_pow, rename_X]
  exact Equiv.sum_comp e (fun i => X i ^ p i)

/-- Coordinate permutation on the actual Fermat quotient rings. -/
def ambientReindex : AmbientRing (fun i => p (e i)) ≃ₐ[ℂ] AmbientRing p :=
  Ideal.quotientEquivAlg _ _ (renameEquiv ℂ e) (by
    simp only [fermatIdeal, Ideal.map_span, Set.image_singleton]
    change Ideal.span {fermat p} = Ideal.span {rename e (fermat (fun i => p (e i)))}
    rw [rename_fermat_reindex])

@[simp] theorem ambientReindex_quotient (f : MvPolynomial (Fin n) ℂ) :
    ambientReindex p e (ambientQuotient (fun i => p (e i)) f) =
      ambientQuotient p (rename e f) := rfl

theorem degreeReindex_weight (d : Fin n →₀ ℕ) :
    Finsupp.weight (xDegree p) (d.mapDomain e) =
      degreeReindex p e (Finsupp.weight (xDegree (fun i => p (e i))) d) := by
  rw [Finsupp.weight_eq_sum]
  rw [← Equiv.sum_comp e (fun i => d.mapDomain e i • xDegree p i)]
  simp only [Finsupp.mapDomain_apply_of_injective e.injective]
  simp only [Finsupp.weight_eq_sum, map_sum, map_nsmul, degreeReindex_x]

theorem homogeneous_reindex_iff (f : MvPolynomial (Fin n) ℂ)
    (l : DegreeGroup (fun i => p (e i))) :
    IsWeightedHomogeneous (xDegree p) (rename e f) (degreeReindex p e l) ↔
      IsWeightedHomogeneous (xDegree (fun i => p (e i))) f l := by
  constructor
  · intro h d hd
    apply (degreeReindex p e).injective
    rw [← degreeReindex_weight]
    apply h
    simpa only [coeff_rename_mapDomain e e.injective] using hd
  · intro h d hd
    obtain ⟨c, rfl⟩ := Finsupp.mapDomain_surjective e.surjective d
    rw [degreeReindex_weight, h (by simpa only [coeff_rename_mapDomain e e.injective] using hd)]

theorem ambientPiece_reindex_iff (l : DegreeGroup (fun i => p (e i)))
    (z : AmbientRing (fun i => p (e i))) :
    ambientReindex p e z ∈ ambientPiece p (degreeReindex p e l) ↔
      z ∈ ambientPiece (fun i => p (e i)) l := by
  constructor
  · rintro ⟨f, hf, he⟩
    refine Submodule.mem_map.mpr ⟨(renameEquiv ℂ e).symm f, ?_, ?_⟩
    · apply (homogeneous_reindex_iff p e _ l).mp
      change IsWeightedHomogeneous (xDegree p)
        ((renameEquiv ℂ e) ((renameEquiv ℂ e).symm f)) (degreeReindex p e l)
      rw [AlgEquiv.apply_symm_apply]
      exact hf
    · apply (ambientReindex p e).injective
      change ambientReindex p e (ambientQuotient (fun i => p (e i))
        ((renameEquiv ℂ e).symm f)) = ambientReindex p e z
      rw [ambientReindex_quotient]
      exact (congrArg (ambientQuotient p) ((renameEquiv ℂ e).apply_symm_apply f)).trans he
  · rintro ⟨f, hf, rfl⟩
    exact Submodule.mem_map.mpr ⟨rename e f, (homogeneous_reindex_iff p e f l).mpr hf,
      (ambientReindex_quotient p e f).symm⟩

end CanonicalRoots
