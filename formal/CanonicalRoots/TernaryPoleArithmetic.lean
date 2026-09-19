import CanonicalRoots.TernaryPlaneArithmetic
import CanonicalRoots.HypersurfaceNumerics

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem ternary_third_coordinate (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
  have h : ∀ i j : Fin 3, i ≠ j →
      ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by decide +kernel
  exact h i j hij

theorem ternary_sum_of_distinct (w : Fin 3 → ℕ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ l, w l) = w i + w j + w k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.sum_univ_three] <;> omega

theorem primitive_ternary_common_divisor (w : Fin 3 → ℕ)
    (hprimitive : Finset.univ.gcd w = 1) (d : ℕ) (hd : ∀ i, d ∣ w i) : d = 1 := by
  have h := Finset.dvd_gcd (s := Finset.univ) (f := w) (fun i _ => hd i)
  rw [hprimitive] at h
  exact Nat.dvd_one.mp h

/-- Pair stabilizer orders are coprime to the positive defect. -/
theorem ternary_pair_gcd_coprime_defect {a h : ℕ} (w : Fin 3 → ℕ)
    (hprimitive : Finset.univ.gcd w = 1) (hdef : h = a + ∑ l, w l)
    (hpair : ∀ i j, i ≠ j → Nat.gcd (w i) (w j) ∣ h)
    (i j : Fin 3) (hij : i ≠ j) : Nat.Coprime a (Nat.gcd (w i) (w j)) := by
  obtain ⟨k, hik, hjk, hall⟩ := ternary_third_coordinate i j hij
  let d := Nat.gcd a (Nat.gcd (w i) (w j))
  have hda : d ∣ a := Nat.gcd_dvd_left _ _
  have hdi : d ∣ w i := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hdj : d ∣ w j := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hdh : d ∣ h := (Nat.gcd_dvd_right _ _).trans (hpair i j hij)
  have hdk : d ∣ w k := by
    rw [hdef, ternary_sum_of_distinct w i j k hij hik hjk, ← add_assoc] at hdh
    exact (Nat.dvd_add_iff_right (dvd_add (dvd_add hda hdi) hdj)).mpr
      (by simpa only [add_assoc] using hdh)
  exact primitive_ternary_common_divisor w hprimitive d (fun l => by
    rcases hall l with rfl | rfl | rfl
    · exact hdi
    · exact hdj
    · exact hdk)

/-- At an axis lying on the hypersurface, the vertex order is also coprime
to the defect. The arrow is supplied by actual isolatedness. -/
theorem isolated_ternary_vertex_coprime_defect {a h : ℕ}
    (f : MvPolynomial (Fin 3) ℂ) (hf : IsolatedAtOrigin f)
    (hlinear : HasNoConstantOrLinear f) (w : Fin 3 → ℕ) (hw : ∀ i, 0 < w i)
    (hhom : IsWeightedHomogeneous w f h) (hprimitive : Finset.univ.gcd w = 1)
    (hdef : h = a + ∑ l, w l) (i : Fin 3) (hi : ¬ w i ∣ h) : Nat.Coprime a (w i) := by
  obtain ⟨j, m, hm, hc⟩ := isolated_axis_coefficient f hf hlinear i
  have he : m * w i + w j = h := by
    simpa only [map_add, Finsupp.weight_single, smul_eq_mul, one_mul] using hhom hc
  have hij : i ≠ j := by
    rintro rfl
    exact hi (he ▸ dvd_add (dvd_mul_left _ _) (dvd_refl _))
  obtain ⟨k, hik, hjk, hall⟩ := ternary_third_coordinate i j hij
  have hwik : Nat.Coprime (w i) (w k) := by
    let g := Nat.gcd (w i) (w k)
    have hgi : g ∣ w i := Nat.gcd_dvd_left _ _
    have hgk : g ∣ w k := Nat.gcd_dvd_right _ _
    have hgh : g ∣ h := isolated_ternary_pair_gcd_dvd f hf hlinear w hw hhom i k hik
    have hgj : g ∣ w j := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hgi m)).mpr (he ▸ hgh)
    exact primitive_ternary_common_divisor w hprimitive g (fun l => by
      rcases hall l with rfl | rfl | rfl
      · exact hgi
      · exact hgj
      · exact hgk)
  have hsum := ternary_sum_of_distinct w i j k hij hik hjk
  have he' : a + w i + w k = m * w i := by omega
  let d := Nat.gcd a (w i)
  have hda : d ∣ a := Nat.gcd_dvd_left _ _
  have hdi : d ∣ w i := Nat.gcd_dvd_right _ _
  have hdk : d ∣ w k := (Nat.dvd_add_iff_right (dvd_add hda hdi)).mpr
    (he'.symm ▸ dvd_mul_of_dvd_right hdi m)
  exact Nat.eq_one_of_dvd_coprimes hwik hdi hdk

end CanonicalRoots
