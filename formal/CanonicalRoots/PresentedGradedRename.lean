import CanonicalRoots.BoundedMonomialBasis
import CanonicalRoots.GradedEquivComposition

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem exponentWeight_rename {n : ℕ} (w : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (d : Fin n →₀ ℕ) : Finsupp.weight (w ∘ σ.symm) (d.mapDomain σ) = Finsupp.weight w d := by
  rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
  rw [← Equiv.sum_comp σ (fun i => d.mapDomain σ i • (w ∘ σ.symm) i)]
  simp only [Finsupp.mapDomain_apply_of_injective σ.injective, Function.comp_apply,
    Equiv.symm_apply_apply]

theorem homogeneous_rename_weights_iff {n : ℕ} (w : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (f : MvPolynomial (Fin n) ℂ) (m : ℕ) :
    IsWeightedHomogeneous (w ∘ σ.symm) (rename σ f) m ↔ IsWeightedHomogeneous w f m := by
  constructor
  · intro h d hd
    rw [← exponentWeight_rename w σ d]
    apply h
    simpa only [coeff_rename_mapDomain σ σ.injective] using hd
  · intro h d hd
    obtain ⟨b,rfl⟩ := Finsupp.mapDomain_surjective σ.surjective d
    rw [exponentWeight_rename, h (by simpa only [coeff_rename_mapDomain σ σ.injective] using hd)]

theorem presentedPiece_rename_iff {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (m : ℕ) (x : PresentedRing f) :
    presentedRenameEquiv f σ x ∈ presentedPiece (rename σ f) (w ∘ σ.symm) m ↔
      x ∈ presentedPiece f w m := by
  constructor
  · rintro ⟨g,hg,he⟩
    refine Submodule.mem_map.mpr ⟨(renameEquiv ℂ σ).symm g,?_,?_⟩
    · apply (homogeneous_rename_weights_iff w σ _ m).mp
      change IsWeightedHomogeneous (w ∘ σ.symm)
        ((renameEquiv ℂ σ) ((renameEquiv ℂ σ).symm g)) m
      rw [AlgEquiv.apply_symm_apply]
      exact hg
    · apply (presentedRenameEquiv f σ).injective
      change presentedRenameEquiv f σ ((Ideal.Quotient.mkₐ ℂ (Ideal.span {f}))
        ((renameEquiv ℂ σ).symm g)) = presentedRenameEquiv f σ x
      rw [presentedRenameEquiv_mk]
      exact (congrArg (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename σ f}))
        ((renameEquiv ℂ σ).apply_symm_apply g)).trans he
  · rintro ⟨g,hg,rfl⟩
    exact Submodule.mem_map.mpr ⟨rename σ g,(homogeneous_rename_weights_iff w σ g m).mpr hg,
      (presentedRenameEquiv_mk f σ g).symm⟩

def presentedGradedRename {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    GradedAlgEquiv (presentedPiece f w) (presentedPiece (rename σ f) (w ∘ σ.symm)) where
  toAlgEquiv := presentedRenameEquiv f σ
  preserves m x := (presentedPiece_rename_iff f w σ m x).symm

theorem noConstantOrLinear_rename {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : HasNoConstantOrLinear f) (σ : Equiv.Perm (Fin n)) :
    HasNoConstantOrLinear (rename σ f) := by
  constructor
  · simpa only [Finsupp.mapDomain_zero, hf.1] using coeff_rename_mapDomain σ σ.injective f 0
  · intro i
    simpa only [Finsupp.mapDomain_single, Equiv.apply_symm_apply, hf.2] using
      coeff_rename_mapDomain σ σ.injective f (Finsupp.single (σ.symm i) 1)

theorem isolatedAtOrigin_rename {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : IsolatedAtOrigin f) (σ : Equiv.Perm (Fin n)) :
    IsolatedAtOrigin (rename σ f) := by
  intro z
  constructor
  · intro hz
    have hc : ∀ i, eval (z ∘ σ) (pderiv i f) = 0 := by
      intro i
      have hh := hz (σ i)
      rwa [pderiv_rename σ.injective, eval_rename] at hh
    have hh := (hf (z ∘ σ)).mp hc
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using congrFun hh (σ.symm i)
  · rintro rfl i
    have hh := (hf 0).mpr rfl (σ.symm i)
    have hp := pderiv_rename σ.injective (σ.symm i) f
    rw [Equiv.apply_symm_apply] at hp
    rw [hp, eval_rename]
    exact hh

/-- Reordering displayed generators transports the full actual isolated presentation. -/
def RootHypersurfacePresentation.renameGenerators {n : ℕ} {p : Fin n → ℕ} {τ : DegreeGroup p}
    (H : RootHypersurfacePresentation p τ) (σ : Equiv.Perm (Fin n)) :
    RootHypersurfacePresentation p τ where
  weights := H.weights ∘ σ.symm
  weights_pos i := H.weights_pos (σ.symm i)
  relationDegree := H.relationDegree
  relationDegree_pos := H.relationDegree_pos
  polynomial := rename σ H.polynomial
  polynomial_ne_zero := by
    intro h
    exact H.polynomial_ne_zero ((renameEquiv ℂ σ).injective (h.trans (map_zero _).symm))
  homogeneous := (homogeneous_rename_weights_iff H.weights σ H.polynomial H.relationDegree).mpr H.homogeneous
  no_constant_or_linear := noConstantOrLinear_rename H.polynomial H.no_constant_or_linear σ
  isolated := isolatedAtOrigin_rename H.polynomial H.isolated σ
  graded_equiv := (presentedGradedRename H.polynomial H.weights σ).symm.trans H.graded_equiv

end CanonicalRoots
