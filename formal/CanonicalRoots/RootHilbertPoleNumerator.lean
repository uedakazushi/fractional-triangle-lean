import CanonicalRoots.PeriodicPowerSeries
import CanonicalRoots.RootPeriodicSignatureRecovery
import CanonicalRoots.WeightedHypersurfaceHilbert

noncomputable section
namespace CanonicalRoots

def rootComplexHilbertSeries {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) : PowerSeries ℂ :=
  PowerSeries.mk fun m => (Module.finrank ℂ (rootPiece p τ m) : ℂ)

theorem rootComplexHilbertSeries_eq_map {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) :
    rootComplexHilbertSeries p τ = PowerSeries.map (Rat.castHom ℂ) (rootHilbertSeries p τ) := by
  ext m
  simp [rootComplexHilbertSeries, rootHilbertSeries]

theorem RootHypersurfacePresentation.complexHilbertSeries_mul_denominator {n : ℕ}
    (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (P : RootHypersurfacePresentation p τ) :
    rootComplexHilbertSeries p τ * ∏ i, (1 - PowerSeries.X ^ P.weights i) =
      1 - PowerSeries.X ^ P.relationDegree := by
  have h := congrArg (PowerSeries.map (Rat.castHom ℂ)) (P.hilbertSeries_mul_denominator p τ)
  simpa only [rootComplexHilbertSeries_eq_map, map_mul, map_prod, map_sub, map_one,
    map_pow, PowerSeries.map_X] using h

/-- A common-period polynomial numerator for the actual root Hilbert series,
with its values computed by the already proved finite Fourier formula. -/
theorem ternary_root_pole_numerator {a N : ℕ} (p : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (hN : 0 < N) (hd : ∀ i, p i ∣ N) :
    ∃ S : Polynomial ℂ,
      (S : PowerSeries ℂ) = rootComplexHilbertSeries p τ *
        (1 - PowerSeries.X ^ N) * (1 - PowerSeries.X) ^ 2 ∧
      ∀ q : ℂ, q ^ N = 1 → q ≠ 1 → S.eval q = (N : ℂ) * (1 - q) ^ 2 *
        (∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0) := by
  classical
  obtain ⟨b, σ, hσ, rfl, M, hM⟩ := ternary_actual_root_hilbert_tail p hp ha τ hτ
  let f : ℕ → ℂ := fun m => 1 - (rootResidueSum p σ m : ℂ)
  have hf : Function.Periodic f N := by
    intro m
    exact congrArg (fun r : ℚ => 1 - (r : ℂ)) (rootResidueSum_periodic p σ hd m)
  obtain ⟨S, hS, heval⟩ := eventual_linear_periodic_numerator
    (rootComplexHilbertSeries p (normalDegree p b σ))
    (rationalDegree p (fun i => by have := hp.1 i; omega) (normalDegree p b σ)) f hf
    ⟨M, fun m hm => by
      have he := congrArg (fun r : ℚ => (r : ℂ)) (hM m hm)
      simp only [rootComplexHilbertSeries, PowerSeries.coeff_mk]
      change _ = _ * _ + (1 - (rootResidueSum p σ m : ℂ))
      push_cast at he
      simpa only [rootResidueSum, Rat.cast_sum, Rat.cast_div, Rat.cast_intCast,
        Rat.cast_natCast, add_sub_assoc] using he⟩
  refine ⟨S, hS, fun q hq hq1 => ?_⟩
  rw [heval q hq]
  have hg : (∑ j ∈ Finset.range N, q ^ j) = 0 := by rw [geom_sum_eq hq1, hq]; simp
  have hfourier := canonicalRoot_periodic_fourier p (fun i => by have := hp.1 i; omega)
    hN hd b σ (fun i => (hσ i).1) hτ q hq hq1
  have hsum : (∑ j ∈ Finset.range N, f j * q ^ j) =
      -(∑ j ∈ Finset.range N, (∑ i, residueFraction (p i) (σ i) j) * q ^ j) := by
    simp only [f, rootResidueSum_complex, sub_mul, one_mul, Finset.sum_sub_distrib, hg, zero_sub]
  rw [hsum]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp [hN0] at hfourier
  linear_combination (1 - q) ^ 2 * hfourier

/-- The numerator participates in an actual polynomial identity with the
hypersurface denominator; this is the bridge to algebraic pole calculations. -/
theorem RootHypersurfacePresentation.pole_polynomial_identity {a N : ℕ}
    (p : Fin 3 → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (P : RootHypersurfacePresentation p τ)
    (hN : 0 < N) (hd : ∀ i, p i ∣ N) :
    ∃ S : Polynomial ℂ,
      S * ∏ i, (1 - Polynomial.X ^ P.weights i) =
        (1 - Polynomial.X ^ P.relationDegree) * (1 - Polynomial.X ^ N) *
          (1 - Polynomial.X) ^ 2 ∧
      ∀ q : ℂ, q ^ N = 1 → q ≠ 1 → S.eval q = (N : ℂ) * (1 - q) ^ 2 *
        (∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0) := by
  obtain ⟨S, hS, heval⟩ := ternary_root_pole_numerator p hp ha τ hτ hN hd
  refine ⟨S, ?_, heval⟩
  apply Polynomial.coe_injective ℂ
  change Polynomial.coeToPowerSeries.ringHom
    (S * ∏ i, (1 - Polynomial.X ^ P.weights i)) =
      Polynomial.coeToPowerSeries.ringHom
        ((1 - Polynomial.X ^ P.relationDegree) * (1 - Polynomial.X ^ N) *
          (1 - Polynomial.X) ^ 2)
  simp only [map_mul, map_prod, map_sub, map_one, map_pow,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [hS]
  calc
    _ = (rootComplexHilbertSeries p τ * ∏ i, (1 - PowerSeries.X ^ P.weights i)) *
      (1 - PowerSeries.X ^ N) * (1 - PowerSeries.X) ^ 2 := by ring
    _ = _ := by rw [P.complexHilbertSeries_mul_denominator]

end CanonicalRoots
