import CanonicalRoots.PresentedCotangentCoordinates
import CanonicalRoots.PresentedGradedOrigin
import CanonicalRoots.IdealCotangentEquiv
import CanonicalRoots.LinearEquivCoordinateMatching

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- A graded equivalence of minimal homogeneous hypersurface presentations
preserves the multiset of coordinate weights. -/
theorem gradedEquiv_weights_permutation {n : ℕ} (f g : MvPolynomial (Fin n) ℂ)
    (hf : HasNoConstantOrLinear f) (hg : HasNoConstantOrLinear g)
    (w v : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (e : GradedAlgEquiv (presentedPiece f w) (presentedPiece g v)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w i = v (σ i) := by
  classical
  let F := presentedOriginCotangentEquiv f hf
  let G := presentedOriginCotangentEquiv g hg
  have he := presentedGradedEquiv_origin_ideal f g hf.1 hg.1 w v hw e
  let E := idealCotangentEquiv (presentedOriginIdeal f) (presentedOriginIdeal g) e.toAlgEquiv he
  let L := F.symm.trans (E.trans G)
  have hzero (i j : Fin n) (hji : v j ≠ w i) : L (Pi.single i 1) j = 0 := by
    have hx : F.symm (Pi.single i 1) =
        (presentedOriginIdeal f).toCotangent (presentedOriginCoordinate f i) := by
      apply F.injective
      rw [F.apply_symm_apply]
      exact (presentedOriginCotangentEquiv_coordinate f hf i).symm
    simp only [L, LinearEquiv.trans_apply, hx]
    change G (idealCotangentEquiv (presentedOriginIdeal f) (presentedOriginIdeal g)
      e.toAlgEquiv he ((presentedOriginIdeal f).toCotangent (presentedOriginCoordinate f i))) j = 0
    rw [idealCotangentEquiv_mk]
    apply presentedOriginCotangentEquiv_homogeneous g hg v (w i) _ _ j hji
    exact (e.preserves (w i) _).mp (presentedOriginCoordinate_homogeneous f w i)
  obtain ⟨σ, hσ⟩ := linearEquiv_coordinate_matching L
  refine ⟨σ, fun i => ?_⟩
  by_contra hi
  exact hσ i (hzero i (σ i) (Ne.symm hi))

end CanonicalRoots
