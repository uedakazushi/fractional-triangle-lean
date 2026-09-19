import CanonicalRoots.RootTwoCoordinateNonregular

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n a : ℕ} (p : Fin (n + 1) → ℕ)

/-- The coordinates of every actual Fermat quotient point satisfy its defining equation. -/
theorem fermatPoint_coordinates_relation (z : AmbientRing p →ₐ[ℂ] ℂ) :
    ∑ l, z (ambientQuotient p (X l)) ^ p l = 0 := by
  have h : ambientQuotient p (fermat p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [fermat, map_sum, map_pow, map_zero] using congrArg z h

/-- Every actual quotient point is recovered by the coordinate evaluation used by the formal chart. -/
theorem fermatPoint_of_coordinates (z : AmbientRing p →ₐ[ℂ] ℂ) :
    fermatPoint p (fun l => z (ambientQuotient p (X l))) (fermatPoint_coordinates_relation p z) = z := by
  have he : (fermatPoint p (fun l => z (ambientQuotient p (X l)))
      (fermatPoint_coordinates_relation p z)).comp (ambientQuotient p) = z.comp (ambientQuotient p) := by
    apply MvPolynomial.algHom_ext
    intro l
    exact fermatPoint_X p (fun l => z (ambientQuotient p (X l)))
      (fermatPoint_coordinates_relation p z) l
  apply AlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (fermatIdeal p) x
  exact DFunLike.congr_fun he f

variable (τ : DegreeGroup p) (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
/-- In at least four ambient variables, a common factor of two tail exponents produces
an actual nonorigin nonregular point of the original root ring. -/
theorem root_nonregular_point_exists_of_tail_gcd (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j)
    (hs : 2 ≤ Nat.gcd (p i.succ) (p j.succ)) :
    ∃ z : AmbientRing p →ₐ[ℂ] ℂ,
      rootPoint p τ z ≠ rootOriginPoint p (fun k => lt_of_lt_of_le (by decide) (hp.1 k)) τ ∧
      ¬ IsRegularLocalRing (AugmentationLocalRing (rootPoint p τ z)) := by
  obtain ⟨z, hi, hj, hz⟩ := twoCoordinatePoint_exists p
    (fun k => lt_of_lt_of_le (by decide) (hp.1 k)) hn i.succ j.succ (by simpa using hij)
  have h := rootTwoCoordinate_nonorigin_nonregular p τ hp ha hτ
    (fun l => z (ambientQuotient p (X l))) (fermatPoint_coordinates_relation p z)
    i j hij hi hj hz hs
  rw [fermatPoint_of_coordinates] at h
  exact ⟨z, h⟩

end CanonicalRoots
