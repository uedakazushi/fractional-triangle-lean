import CanonicalRoots.RootVertexProfile

noncomputable section
open CanonicalRoots

-- A nonconstant periodic sequence: the sign and period in the denominator matter.
example : PowerSeries.mk (fun m : ℕ => (-1 : ℂ) ^ m) * (1 - PowerSeries.X ^ 2) =
    1 - PowerSeries.X := by
  rw [periodicPowerSeries_mul_one_sub _ (by intro m; simp [pow_add])]
  ext m
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_mk,
    map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X]
  rcases m with _ | _ | m <;> simp <;> omega

-- At -1 the signature (2,3,7) contributes 1/4; exactly two Fermat weights vanish.
example : (∑ i : Fin 3, if (-1 : ℂ) ^ (![2,3,7] : Fin 3 → ℕ) i = 1 then
    1 / (((![2,3,7] : Fin 3 → ℕ) i : ℂ) * (1 - (-1 : ℂ) ^ (-1 : ℤ))) else 0) = 1 / 4 := by
  norm_num [Fin.sum_univ_succ]

example : (42 : ℂ) / (14 * 6 * (1 - (-1 : ℂ) ^ 21)) = 1 / 4 := by norm_num

-- The polynomial bridge is available for arbitrary actual presentations and every common period.
example {a N : ℕ} (p : Fin 3 → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (P : RootHypersurfacePresentation p τ)
    (hN : 0 < N) (hd : ∀ i, p i ∣ N) :
    ∃ S : Polynomial ℂ,
      S * ∏ i, (1 - Polynomial.X ^ P.weights i) =
        (1 - Polynomial.X ^ P.relationDegree) * (1 - Polynomial.X ^ N) *
          (1 - Polynomial.X) ^ 2 ∧
      ∀ q : ℂ, q ^ N = 1 → q ≠ 1 → S.eval q = (N : ℂ) * (1 - q) ^ 2 *
        (∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0) :=
  P.pole_polynomial_identity p hp ha τ hτ hN hd

-- Clearing the defect factor changes the -1 residue 1/4 to the divisor sum 1/2.
example : signatureDivisorProfile ([2,3,7] : Multiset ℕ) 2 = (42 : ℚ) / (14 * 6) := by
  norm_num [signatureDivisorProfile_eq_sum]

-- Repeated signature entries contribute repeatedly to the recovered profile.
example : signatureDivisorProfile ([3,3,4] : Multiset ℕ) 3 = (2 : ℚ) / 3 := by
  norm_num [signatureDivisorProfile_eq_sum]

example {a e : ℕ} (t : Target 3 a) (he : 2 ≤ e)
    (hA : e ∣ t.presentation.weights 0)
    (hB : ¬ e ∣ t.presentation.weights 1) (hC : ¬ e ∣ t.presentation.weights 2) :
    signatureDivisorProfile (List.ofFn t.signature : Multiset ℕ) e =
      if t.presentation.weights 0 ∣ t.presentation.relationDegree then 0
      else (t.presentation.weights 0 : ℚ)⁻¹ :=
  t.ternary_profile_single_weight he (Equiv.refl _) hA hB hC

end
