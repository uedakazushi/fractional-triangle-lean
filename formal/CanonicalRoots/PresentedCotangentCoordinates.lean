import CanonicalRoots.PresentedCotangent

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : HasNoConstantOrLinear f)

theorem presentedOriginCotangentEquiv_mk (g : polynomialOriginIdeal n) :
    presentedOriginCotangentEquiv f hf ((presentedOriginIdeal f).toCotangent
      ⟨Ideal.Quotient.mk (Ideal.span {f}) (g : MvPolynomial (Fin n) ℂ),
        Ideal.mem_map_of_mem _ g.property⟩) = originLinearPart n g := by
  let E := quotientCotangentEquiv (polynomialOriginIdeal n)
    (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) (Ideal.Quotient.mkₐ_surjective ℂ _)
    (presented_ker_le_origin_square f hf)
  change polynomialOriginCotangentEquiv n (E.symm (E ((polynomialOriginIdeal n).toCotangent g))) = _
  rw [E.symm_apply_apply]
  rfl

def presentedOriginCoordinate (i : Fin n) : presentedOriginIdeal f :=
  ⟨Ideal.Quotient.mk (Ideal.span {f}) (X i), Ideal.mem_map_of_mem _
    ((mem_polynomialOriginIdeal_iff _).mpr (by simp))⟩

theorem presentedOriginCotangentEquiv_coordinate (i : Fin n) :
    presentedOriginCotangentEquiv f hf ((presentedOriginIdeal f).toCotangent
      (presentedOriginCoordinate f i)) = Pi.single i 1 := by
  classical
  have he := presentedOriginCotangentEquiv_mk f hf
    ⟨X i, (mem_polynomialOriginIdeal_iff _).mpr (by simp)⟩
  calc
    _ = originLinearPart n ⟨X i, (mem_polynomialOriginIdeal_iff _).mpr (by simp)⟩ := he
    _ = _ := by
      ext j
      simp only [originLinearPart_apply, coeff_X, Pi.single_apply, Finsupp.single_left_inj one_ne_zero]
      simp only [eq_comm]

theorem presentedOriginCoordinate_homogeneous (w : Fin n → ℕ) (i : Fin n) :
    (presentedOriginCoordinate f i : PresentedRing f) ∈ presentedPiece f w (w i) :=
  Submodule.mem_map.mpr ⟨X i, isWeightedHomogeneous_X ℂ w i, rfl⟩

theorem presentedOriginCotangentEquiv_homogeneous (w : Fin n → ℕ) (m : ℕ)
    (z : presentedOriginIdeal f) (hz : (z : PresentedRing f) ∈ presentedPiece f w m)
    (i : Fin n) (hi : w i ≠ m) :
    presentedOriginCotangentEquiv f hf ((presentedOriginIdeal f).toCotangent z) i = 0 := by
  obtain ⟨g, hg, he⟩ := Submodule.mem_map.mp hz
  change Ideal.Quotient.mk (Ideal.span {f}) g = (z : PresentedRing f) at he
  have hz0 : presentedAugmentation f hf.1 (z : PresentedRing f) = 0 := by
    exact (le_of_eq (presentedOriginIdeal_eq_ker f hf.1)) z.property
  have hg0 : g ∈ polynomialOriginIdeal n := by
    rw [mem_polynomialOriginIdeal_iff, ← presentedAugmentation_mk f hf.1, he]
    exact hz0
  have he' : z = ⟨Ideal.Quotient.mk (Ideal.span {f}) g, Ideal.mem_map_of_mem _ hg0⟩ :=
    Subtype.ext he.symm
  rw [he']
  have heq := congrFun (presentedOriginCotangentEquiv_mk f hf ⟨g, hg0⟩) i
  refine heq.trans ?_
  change g.coeff (Finsupp.single i 1) = 0
  by_contra hn
  apply hi
  simpa only [Finsupp.weight_single, one_smul] using hg hn

end CanonicalRoots
