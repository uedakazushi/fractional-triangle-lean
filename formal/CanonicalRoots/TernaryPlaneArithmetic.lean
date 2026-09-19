import CanonicalRoots.IsolatedCoordinatePlane
import CanonicalRoots.PolynomialCoordinatePermutation

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem isolated_ternary_not_X_dvd {h : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f)
    (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i) (hhom : IsWeightedHomogeneous w f h)
    (j : Fin 3) : ¬ X j ∣ f := by
  classical
  let e : Equiv.Perm (Fin 3) := Equiv.swap j 1
  have hhom' : IsWeightedHomogeneous (fun i => w (e.symm i)) (rename e f) h := by
    apply weightedHomogeneous_rename_perm
    simpa using hhom
  have hnot := isolated_ternary_not_X_one_dvd (rename e f)
    (isolated_rename_perm e f hf) (noConstantOrLinear_rename_perm e f hlinear)
    (fun i => w (e.symm i)) (hw _) hhom'
  rintro ⟨g, rfl⟩
  apply hnot
  refine ⟨rename e g, ?_⟩
  simp [e]

theorem exists_plane_coefficient_of_not_X_dvd {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (j : Fin n) (hf : ¬ X j ∣ f) :
    ∃ d : Fin n →₀ ℕ, d j = 0 ∧ f.coeff d ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply hf
  rw [f.as_sum]
  apply Finset.dvd_sum
  intro d hd
  apply X_dvd_monomial.mpr
  right
  intro hj
  exact mem_support_iff.mp hd (hn d hj)

/-- Every coordinate-plane restriction contains an actual nonzero coefficient. -/
theorem isolated_ternary_plane_coefficient {h : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f)
    (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i) (hhom : IsWeightedHomogeneous w f h)
    (j : Fin 3) : ∃ d : Fin 3 →₀ ℕ, d j = 0 ∧ f.coeff d ≠ 0 :=
  exists_plane_coefficient_of_not_X_dvd f j
    (isolated_ternary_not_X_dvd f hf hlinear w hw hhom j)

/-- The pairwise gcd divisibility needed for the coordinate-pole calculation
follows from isolatedness, not an added arithmetic assumption. -/
theorem isolated_ternary_pair_gcd_dvd {h : ℕ} (f : MvPolynomial (Fin 3) ℂ)
    (hf : IsolatedAtOrigin f) (hlinear : HasNoConstantOrLinear f)
    (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i) (hhom : IsWeightedHomogeneous w f h)
    (i j : Fin 3) (hij : i ≠ j) : Nat.gcd (w i) (w j) ∣ h := by
  have hthree : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3,
      k ≠ i ∧ k ≠ j ∧ ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by decide +kernel
  obtain ⟨k, hki, hkj, hall⟩ := hthree i j hij
  obtain ⟨d, hdk, hd⟩ := isolated_ternary_plane_coefficient f hf hlinear w hw hhom k
  rw [← hhom hd, Finsupp.weight_eq_sum]
  apply Finset.dvd_sum
  intro l hl
  rcases hall l with rfl | rfl | rfl
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  · simp [hdk]

end CanonicalRoots
