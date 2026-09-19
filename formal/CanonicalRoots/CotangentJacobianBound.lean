import CanonicalRoots.PolynomialPointCotangent

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n : ℕ} {B : Type*} [CommRing B] [Algebra ℂ B]

/-- A defining relation with a nonzero partial derivative removes at least one
cotangent direction at the actual complex point. -/
theorem cotangent_finrank_lt_of_derivative
    (ε : B →ₐ[ℂ] ℂ) (q : MvPolynomial (Fin n) ℂ →ₐ[ℂ] B)
    (hq : Function.Surjective q) (v : Fin n → ℂ) (hε : ε.comp q = polynomialPoint v)
    (f : MvPolynomial (Fin n) ℂ) (hf : q f = 0) (i : Fin n)
    (hi : polynomialPoint v (pderiv i f) ≠ 0) :
    Module.finrank ℂ (RingHom.ker ε.toRingHom).Cotangent < n := by
  let J := RingHom.ker (polynomialPoint v).toRingHom
  let I := RingHom.ker ε.toRingHom
  have heval (g : MvPolynomial (Fin n) ℂ) : ε (q g) = polynomialPoint v g :=
    AlgHom.congr_fun hε g
  have hmap : J ≤ I.comap q := by
    intro g hg
    change ε (q g) = 0
    rw [heval]
    exact hg
  let F := Ideal.mapCotangent J I q hmap
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := I.toCotangent_surjective z
    obtain ⟨g, rfl⟩ := hq y
    have hg : g ∈ J := by
      change polynomialPoint v g = 0
      rw [← heval]
      exact hy
    exact ⟨J.toCotangent ⟨g, hg⟩, rfl⟩
  have hfJ : polynomialPoint v f = 0 := by rw [← heval, hf, map_zero]
  let x : J.Cotangent := J.toCotangent ⟨f, hfJ⟩
  have hx : x ≠ 0 := pointCotangent_ne_zero_of_derivative v f hfJ i hi
  have hxker : x ∈ F.ker := by
    change I.toCotangent ⟨q f, hmap hfJ⟩ = 0
    have hz : (⟨q f, hmap hfJ⟩ : I) = 0 := Subtype.ext hf
    rw [hz, map_zero]
  let : FiniteDimensional ℂ J.Cotangent :=
    FiniteDimensional.of_injective (polynomialPointCotangentEquiv v).toLinearMap
      (polynomialPointCotangentEquiv v).injective
  have hk : F.ker ≠ ⊥ := by
    intro he
    rw [he] at hxker
    exact hx hxker
  have hpos : 1 ≤ Module.finrank ℂ F.ker := Submodule.one_le_finrank_iff.mpr hk
  have hdim := F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hF, finrank_top,
    polynomialPointCotangent_finrank] at hdim
  change Module.finrank ℂ I.Cotangent < n
  omega

end CanonicalRoots
