import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem weightedComponent_mul_homogeneous {n : ℕ} (w : Fin n → ℕ)
    (f g : MvPolynomial (Fin n) ℂ) (h m : ℕ) (hf : IsWeightedHomogeneous w f h) :
    weightedHomogeneousComponent w m (f * g) =
      if h ≤ m then f * weightedHomogeneousComponent w (m - h) g else 0 := by
  have he := DirectSum.coe_decompose_mul_of_left_mem
    (weightedHomogeneousSubmodule ℂ w) m (b := g) hf
  change (decompose' ℂ w (f * g) m : MvPolynomial (Fin n) ℂ) =
    if h ≤ m then f * (decompose' ℂ w g (m - h) : MvPolynomial (Fin n) ℂ) else 0 at he
  simpa only [decompose'_apply] using he

theorem weightedPiece_finite {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (m : ℕ) :
    Module.Finite ℂ (weightedHomogeneousSubmodule ℂ w m) :=
  Module.Finite.iff_fg.mpr (weightedHomogeneousSubmodule_fg ℂ w (fun i => ne_of_gt (hw i)) m)

def weightedQuotientMap {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ) (m : ℕ) :
    weightedHomogeneousSubmodule ℂ w m →ₗ[ℂ] presentedPiece f w m where
  toFun x := ⟨Ideal.Quotient.mkₐ ℂ (Ideal.span {f}) x,
    Submodule.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

theorem weightedQuotientMap_surjective {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (m : ℕ) : Function.Surjective (weightedQuotientMap f w m) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, hq⟩ := Submodule.mem_map.mp hx
  exact ⟨⟨g, hg⟩, Subtype.ext hq⟩

theorem presentedPiece_finite {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (m : ℕ) :
    Module.Finite ℂ (presentedPiece f w m) := by
  let := weightedPiece_finite w hw m
  exact Module.Finite.of_surjective (weightedQuotientMap f w m)
    (weightedQuotientMap_surjective f w m)

def weightedMultiply {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ)
    (h : ℕ) (hf : IsWeightedHomogeneous w f h) (m : ℕ) :
    weightedHomogeneousSubmodule ℂ w m →ₗ[ℂ] weightedHomogeneousSubmodule ℂ w (h + m) where
  toFun x := ⟨f * x.val, hf.mul x.property⟩
  map_add' _ _ := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact mul_smul_comm _ _ _

theorem weightedMultiply_injective {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ)
    (h : ℕ) (hf : IsWeightedHomogeneous w f h) (hne : f ≠ 0) (m : ℕ) :
    Function.Injective (weightedMultiply f w h hf m) := by
  intro x y hxy
  exact Subtype.ext (mul_left_cancel₀ hne (congrArg Subtype.val hxy))

/-- The degree-wise kernel is exactly multiplication by the actual defining polynomial. -/
theorem weightedQuotientMap_ker {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ)
    (h : ℕ) (hf : IsWeightedHomogeneous w f h) (m : ℕ) :
    LinearMap.ker (weightedQuotientMap f w (h + m)) =
      LinearMap.range (weightedMultiply f w h hf m) := by
  ext x
  constructor
  · intro hx
    have hz : Ideal.Quotient.mkₐ ℂ (Ideal.span {f}) x.val = 0 := congrArg Subtype.val hx
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hc := congrArg (weightedHomogeneousComponent w (h + m)) hg
    rw [weightedComponent_mul_homogeneous w f g h (h + m) hf,
      ite_eq_left (Nat.le_add_right h m), Nat.add_sub_cancel_left,
      x.property.weightedHomogeneousComponent_same] at hc
    exact ⟨⟨weightedHomogeneousComponent w m g, weightedHomogeneousComponent_mem w g m⟩,
      Subtype.ext hc.symm⟩
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    change Ideal.Quotient.mkₐ ℂ (Ideal.span {f}) (f * g.val) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨g.val, rfl⟩

theorem weightedQuotientMap_injective_below {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (h : ℕ) (hf : IsWeightedHomogeneous w f h) (m : ℕ) (hm : m < h) :
    Function.Injective (weightedQuotientMap f w m) := by
  apply (weightedQuotientMap f w m).ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hz : Ideal.Quotient.mkₐ ℂ (Ideal.span {f}) x.val = 0 := congrArg Subtype.val hx
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hc := congrArg (weightedHomogeneousComponent w m) hg
  rw [weightedComponent_mul_homogeneous w f g h m hf, ite_eq_right (by omega),
    x.property.weightedHomogeneousComponent_same] at hc
  exact Subtype.ext hc

/-- Rank-nullity for the actual homogeneous quotient, including degrees below the relation. -/
theorem presentedPiece_finrank_add {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (h : ℕ)
    (hf : IsWeightedHomogeneous w f h) (hne : f ≠ 0) (m : ℕ) :
    Module.finrank ℂ (presentedPiece f w m) +
      (if h ≤ m then Module.finrank ℂ (weightedHomogeneousSubmodule ℂ w (m - h)) else 0) =
      Module.finrank ℂ (weightedHomogeneousSubmodule ℂ w m) := by
  by_cases hm : h ≤ m
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    let := weightedPiece_finite w hw (h + k)
    have he := LinearMap.finrank_range_add_finrank_ker (weightedQuotientMap f w (h + k))
    rw [LinearMap.range_eq_top.mpr (weightedQuotientMap_surjective f w (h + k)),
      finrank_top, weightedQuotientMap_ker f w h hf k,
      LinearMap.finrank_range_of_inj (weightedMultiply_injective f w h hf hne k)] at he
    rw [ite_eq_left (Nat.le_add_right h k), Nat.add_sub_cancel_left]
    exact he
  · rw [ite_eq_right hm, add_zero]
    exact (LinearEquiv.ofBijective (weightedQuotientMap f w m)
      ⟨weightedQuotientMap_injective_below f w h hf m (by omega),
        weightedQuotientMap_surjective f w m⟩).finrank_eq.symm

end CanonicalRoots
