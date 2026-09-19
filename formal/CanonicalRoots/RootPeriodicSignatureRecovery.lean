import CanonicalRoots.RootPeriodSignatureProfile
import CanonicalRoots.TernaryHilbertPeriodComparison

noncomputable section
namespace CanonicalRoots

theorem rootResidueSum_complex {n : ℕ} (p : Fin n → ℕ) (σ : Fin n → ℤ) (m : ℕ) :
    (rootResidueSum p σ m : ℂ) = ∑ i, residueFraction (p i) (σ i) m := by
  unfold rootResidueSum residueFraction rootResidue
  push_cast
  rfl

/-- Equality of the actual periodic residue terms recovers the signature multiset,
using primitive roots only as algebraic finite Fourier evaluation points. -/
theorem root_periodic_signature_recovery {n m a N : ℕ} (p : Fin n → ℕ) (q : Fin m → ℕ)
    (hp : ∀ i, 2 ≤ p i) (hq : ∀ i, 2 ≤ q i)
    (b c : ℤ) (σ : Fin n → ℤ) (ρ : Fin m → ℤ)
    (hσ : ∀ i, 0 ≤ σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hrootp : IsCanonicalRoot p a (normalDegree p b σ))
    (hrootq : IsCanonicalRoot q a (normalDegree q c ρ))
    (hN : 0 < N) (hdp : ∀ i, p i ∣ N) (hdq : ∀ i, q i ∣ N)
    (heq : rootResidueSum p σ = rootResidueSum q ρ) :
    (List.ofFn p : Multiset ℕ) = (List.ofFn q : Multiset ℕ) := by
  classical
  apply signature_eq_of_divisorProfile
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa using hr)
    exact hp i
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa using hr)
    exact hq i
  intro e he
  by_cases hd : (∃ i, e ∣ p i) ∨ (∃ i, e ∣ q i)
  · let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / e)
    have hζ : IsPrimitiveRoot ζ e := Complex.isPrimitiveRoot_exp e (by omega)
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
    have heN : e ∣ N := by
      rcases hd with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hi.trans (hdp i)
      · exact hi.trans (hdq i)
    have hden : 1 - ζ ^ (-(a : ℤ)) ≠ 0 := by
      rcases hd with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact (canonicalRoot_coordinate_fourier p (fun i => by have := hp i; omega) b σ hσ
          hrootp i ζ ((hζ.pow_eq_one_iff_dvd _).mpr hi) hζ1).1
      · exact (canonicalRoot_coordinate_fourier q (fun i => by have := hq i; omega) c ρ hρ
          hrootq i ζ ((hζ.pow_eq_one_iff_dvd _).mpr hi) hζ1).1
    have hpF := canonicalRoot_periodic_signature_profile p (fun i => by have := hp i; omega)
      hN hdp b σ hσ hrootp ζ hζ he heN
    have hqF := canonicalRoot_periodic_signature_profile q (fun i => by have := hq i; omega)
      hN hdq c ρ hρ hrootq ζ hζ he heN
    have hterm (j : ℕ) : (∑ i, residueFraction (p i) (σ i) j) =
        ∑ i, residueFraction (q i) (ρ i) j := by
      rw [← rootResidueSum_complex, ← rootResidueSum_complex, heq]
    simp_rw [hterm] at hpF
    have hcast := (div_left_inj' hden).mp (hpF.symm.trans hqF)
    exact_mod_cast hcast
  · push Not at hd
    rw [signatureDivisorProfile_ofFn, signatureDivisorProfile_ofFn]
    simp [hd.1, hd.2]

end CanonicalRoots
