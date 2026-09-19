import CanonicalRoots.SignatureDivisorRecovery
import CanonicalRoots.TernaryHilbertTail
import CanonicalRoots.CoordinateFourierPeriod
import CanonicalRoots.RootPeriodFourier

noncomputable section
open CanonicalRoots

-- Repeated orders are counted, rather than converted to a set.
example : signatureDivisorProfile ({2,2,3} : Multiset ℕ) 2 = 1 := by
  rw [signatureDivisorProfile_eq_sum]
  norm_num

example : signatureDivisorProfile ({2,2,3} : Multiset ℕ) 2 ≠
    signatureDivisorProfile ({2,3} : Multiset ℕ) 2 := by
  simp only [signatureDivisorProfile_eq_sum]
  norm_num

-- A signature with shared prime factors still has the proved actual Hilbert tail.
example (τ : DegreeGroup (![2,3,8] : Fin 3 → ℕ))
    (hτ : IsCanonicalRoot ![2,3,8] 1 τ) :
    ∃ b : ℤ, ∃ σ : Fin 3 → ℤ, (∀ i, 0 ≤ σ i ∧ σ i < (![2,3,8] : Fin 3 → ℕ) i) ∧
      τ = normalDegree ![2,3,8] b σ ∧ ∃ M : ℕ, ∀ m ≥ M,
      (Module.finrank ℂ (rootPiece ![2,3,8] τ m) : ℚ) =
        (m : ℚ) * rationalDegree ![2,3,8] (by decide) τ + 1 -
          ∑ i, (rootResidue ![2,3,8] σ m i : ℚ) / (![2,3,8] i : ℚ) := by
  exact ternary_actual_root_hilbert_tail _
    ⟨by decide +kernel, by norm_num [Fin.sum_univ_succ]⟩ (by decide) τ hτ

-- The a=3 congruence 3*2+1=7 controls a Fourier coefficient at arbitrary nontrivial seventh roots.
example (q : ℂ) (hq : q ^ 7 = 1) (hne : q ≠ 1) :
    -(1 / (7 : ℂ) ^ 2) *
      (∑ j : Fin 7, ((((j.val : ℤ) * 2) % 7 : ℤ) : ℂ) * q ^ j.val) =
        1 / (7 * (1 - q ^ (-(3 : ℤ)))) :=
  canonical_residue_fourier (by decide) 2 1 (by decide) (by norm_num) q hq hne

-- A period-seven contribution vanishes at order two, even on a common period fourteen.
example : -(1 / (14 : ℂ)) *
    (∑ j ∈ Finset.range 14, residueFraction 7 2 j * (-1 : ℂ) ^ j) = 0 := by
  have h := canonical_residue_common_period (p := 7) (a := 3) (k := 2)
    (by decide) (by decide) 2 1 (by decide) (by norm_num) (-1) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

-- All coordinates use an arbitrary common period, without assuming pairwise coprimality.
example {n a N : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (hN : 0 < N)
    (hd : ∀ i, p i ∣ N) (b : ℤ) (σ : Fin n → ℤ) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsCanonicalRoot p a (normalDegree p b σ)) (q : ℂ) (hq : q ^ N = 1) (hne : q ≠ 1) :
    -(1 / (N : ℂ)) *
      (∑ j ∈ Finset.range N, (∑ i, residueFraction (p i) (σ i) j) * q ^ j) =
        ∑ i, if q ^ p i = 1 then 1 / ((p i : ℂ) * (1 - q ^ (-(a : ℤ)))) else 0 :=
  canonicalRoot_periodic_fourier p hp hN hd b σ hσ hroot q hq hne

end
