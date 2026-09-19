import CanonicalRoots.LinearPeriodicTail
import CanonicalRoots.TernaryHilbertTail

noncomputable section
namespace CanonicalRoots

def rootResidueSum {n : ℕ} (p : Fin n → ℕ) (σ : Fin n → ℤ) (m : ℕ) : ℚ :=
  ∑ i, (rootResidue p σ m i : ℚ) / (p i : ℚ)

theorem rootResidueSum_periodic {n N : ℕ} (p : Fin n → ℕ) (σ : Fin n → ℤ)
    (hd : ∀ i, p i ∣ N) : Function.Periodic (rootResidueSum p σ) N := by
  intro m
  unfold rootResidueSum
  apply Finset.sum_congr rfl
  intro i hi
  have he : rootResidue p σ (m + N) i = rootResidue p σ m i := by
    unfold rootResidue
    rw [Nat.cast_add, add_mul, Int.add_emod]
    have hd' : (p i : ℤ) ∣ (N : ℤ) * σ i :=
      dvd_mul_of_dvd_left (by exact_mod_cast hd i) _
    rw [Int.emod_eq_zero_of_dvd hd', add_zero, Int.emod_emod]
  rw [he]

/-- Equality of the actual ternary Hilbert functions determines their full
periodic residue term, with no assumption about a hypersurface presentation. -/
theorem ternary_hilbert_periodic_part_eq {a N : ℕ} (p q : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (hq : AdmissibleSignature q) (ha : 1 ≤ a)
    (b c : ℤ) (σ ρ : Fin 3 → ℤ)
    (hrootp : IsCanonicalRoot p a (normalDegree p b σ))
    (hrootq : IsCanonicalRoot q a (normalDegree q c ρ))
    (hN : 0 < N) (hdp : ∀ i, p i ∣ N) (hdq : ∀ i, q i ∣ N)
    (he : ∀ m, Module.finrank ℂ (rootPiece p (normalDegree p b σ) m) =
      Module.finrank ℂ (rootPiece q (normalDegree q c ρ) m)) :
    rootResidueSum p σ = rootResidueSum q ρ := by
  obtain ⟨M, hM⟩ := ternary_root_hilbert_eventual_formula p hp ha b σ hrootp
  obtain ⟨K, hK⟩ := ternary_root_hilbert_eventual_formula q hq ha c ρ hrootq
  have hperp : Function.Periodic (fun m => 1 - rootResidueSum p σ m) N := by
    intro m
    exact congrArg (fun x : ℚ => 1 - x) (rootResidueSum_periodic p σ hdp m)
  have hperq : Function.Periodic (fun m => 1 - rootResidueSum q ρ m) N := by
    intro m
    exact congrArg (fun x : ℚ => 1 - x) (rootResidueSum_periodic q ρ hdq m)
  obtain ⟨_, hfg⟩ := linear_periodic_tail_unique _ _ N hN hperp hperq
    (rationalDegree p (fun i => by have := hp.1 i; omega) (normalDegree p b σ))
    (rationalDegree q (fun i => by have := hq.1 i; omega) (normalDegree q c ρ)) (by
      refine ⟨max M K, fun m hm => ?_⟩
      have hm' := hM m (le_trans (le_max_left _ _) hm)
      have hk' := hK m (le_trans (le_max_right _ _) hm)
      rw [he m] at hm'
      change _ = _ + 1 - rootResidueSum p σ m at hm'
      change _ = _ + 1 - rootResidueSum q ρ m at hk'
      linarith)
  funext m
  have hm := congrFun hfg m
  linarith

end CanonicalRoots
