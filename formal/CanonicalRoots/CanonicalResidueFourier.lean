import CanonicalRoots.FiniteRootFourier
import CanonicalRoots.RootHilbert
import Mathlib.Data.Int.ModEq

noncomputable section
namespace CanonicalRoots

def negativeIndexResidue (p a : ℕ) : ℕ := ((-(a : ℤ)) % p).toNat

theorem negativeIndexResidue_cast (p a : ℕ) (hp : 0 < p) :
    (negativeIndexResidue p a : ℤ) = (-(a : ℤ)) % p :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast ne_of_gt hp))

theorem canonical_residue_inverse_mod {p a : ℕ} (hp : 0 < p) (σ v : ℤ)
    (hσ : 0 ≤ σ) (hv : (a : ℤ) * σ + 1 = (p : ℤ) * v) :
    σ.toNat * negativeIndexResidue p a ≡ 1 [MOD p] := by
  apply Int.natCast_modEq_iff.mp
  rw [Int.natCast_mul, Int.toNat_of_nonneg hσ, negativeIndexResidue_cast p a hp]
  apply Int.modEq_iff_dvd.mpr
  refine ⟨v + σ * ((-(a : ℤ)) / p), ?_⟩
  have he := Int.emod_add_mul_ediv (-(a : ℤ)) (p : ℤ)
  linear_combination hv - σ * he

theorem root_of_unity_negative_index_power {p a : ℕ} (hp : 0 < p)
    (q : ℂ) (hq : q ^ p = 1) :
    q ^ negativeIndexResidue p a = q ^ (-(a : ℤ)) := by
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (ne_of_gt hp)] at hq
    exact zero_ne_one hq
  let z : ℂˣ := Units.mk0 q hq0
  have hz : z ^ p = 1 := by apply Units.ext; simpa [z] using hq
  have he := zpow_eq_zpow_emod' (-(a : ℤ)) hz
  have he' := congrArg (fun u : ℂˣ => (u : ℂ)) he
  rw [← negativeIndexResidue_cast p a hp] at he'
  simpa [z] using he'.symm

/-- The normalized residue Fourier coefficient is forced by the genuine root congruence. -/
theorem canonical_residue_fourier {p a : ℕ} (hp : 0 < p) (σ v : ℤ)
    (hσ : 0 ≤ σ) (hv : (a : ℤ) * σ + 1 = (p : ℤ) * v)
    (q : ℂ) (hq : q ^ p = 1) (hne : q ≠ 1) :
    -(1 / (p : ℂ) ^ 2) *
      (∑ j : Fin p, ((((j.val : ℤ) * σ) % p : ℤ) : ℂ) * q ^ j.val) =
        1 / ((p : ℂ) * (1 - q ^ (-(a : ℤ)))) := by
  have hi := canonical_residue_inverse_mod hp σ v hσ hv
  have hs := residue_weighted_root_sum hp hi q hq hne
  have hc : ∀ j : Fin p, ((((σ.toNat * j.val) % p : ℕ) : ℂ)) =
      ((((j.val : ℤ) * σ) % p : ℤ) : ℂ) := by
    intro j
    have he : (((σ.toNat * j.val) % p : ℕ) : ℤ) = ((j.val : ℤ) * σ) % p := by
      simp [Int.toNat_of_nonneg hσ, mul_comm]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℂ)) he
  simp_rw [hc] at hs
  rw [hs, root_of_unity_negative_index_power hp q hq]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  field_simp

theorem canonical_residue_fourier_denominator_ne_zero {p a : ℕ} (hp : 0 < p) (σ v : ℤ)
    (hσ : 0 ≤ σ) (hv : (a : ℤ) * σ + 1 = (p : ℤ) * v)
    (q : ℂ) (hq : q ^ p = 1) (hne : q ≠ 1) : 1 - q ^ (-(a : ℤ)) ≠ 0 := by
  intro hz
  have hi := canonical_residue_inverse_mod hp σ v hσ hv
  have he := residue_root_power hi q hq 1
  rw [root_of_unity_negative_index_power hp q hq, sub_eq_zero.mp hz |>.symm,
    one_pow, pow_one] at he
  exact hne he.symm

theorem canonicalRoot_coordinate_fourier {n a : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (b : ℤ) (σ : Fin n → ℤ) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsCanonicalRoot p a (normalDegree p b σ)) (i : Fin n)
    (q : ℂ) (hq : q ^ p i = 1) (hne : q ≠ 1) :
    1 - q ^ (-(a : ℤ)) ≠ 0 ∧
    -(1 / (p i : ℂ) ^ 2) *
      (∑ j : Fin (p i), ((((j.val : ℤ) * σ i) % p i : ℤ) : ℂ) * q ^ j.val) =
        1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) := by
  obtain ⟨v, _, hv⟩ := (canonicalRoot_normal_iff p b σ).mp hroot
  exact ⟨canonical_residue_fourier_denominator_ne_zero (hp i) (σ i) (v i) (hσ i) (hv i) q hq hne,
    canonical_residue_fourier (hp i) (σ i) (v i) (hσ i) (hv i) q hq hne⟩

end CanonicalRoots
