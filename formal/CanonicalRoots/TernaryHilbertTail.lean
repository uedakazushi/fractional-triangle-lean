import CanonicalRoots.RootEventualNonvanishing

noncomputable section
namespace CanonicalRoots

theorem normalHilbertCoefficient_two (b : ℤ) (hb : 0 ≤ b) :
    (normalHilbertCoefficient 2 b : ℚ) = (b : ℚ) + 1 := by
  rw [normalHilbertCoefficient, ite_eq_right (not_lt_of_ge hb)]
  have h : 2 + b.toNat - 1 = b.toNat + 1 := by omega
  rw [h, Nat.choose_succ_self_right]
  simp only [Nat.cast_add, Nat.cast_one, add_left_inj]
  exact_mod_cast Int.toNat_of_nonneg hb

/-- The actual ternary root Hilbert function is eventually a linear term plus
the bounded periodic residue terms appearing in the finite Fourier calculation. -/
theorem ternary_root_hilbert_eventual_formula {a : ℕ} (p : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (b : ℤ) (σ : Fin 3 → ℤ)
    (hroot : IsCanonicalRoot p a (normalDegree p b σ)) :
    ∃ M : ℕ, ∀ m ≥ M,
      (Module.finrank ℂ (rootPiece p (normalDegree p b σ) m) : ℚ) =
        (m : ℚ) * rationalDegree p (fun i => by have := hp.1 i; omega) (normalDegree p b σ) + 1 -
          ∑ i, (rootResidue p σ m i : ℚ) / (p i : ℚ) := by
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  obtain ⟨M, hM⟩ := rootCarry_eventually_nonneg p hp ha b σ hroot
  refine ⟨M, fun m hm => ?_⟩
  rw [rootHilbert_formula p hpos b σ m, normalHilbertCoefficient_two _ (hM m hm),
    rootCarry_rational p (fun i => ne_of_gt (hpos i)) b σ m]
  ring

theorem ternary_actual_root_hilbert_tail {a : ℕ} (p : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    ∃ b : ℤ, ∃ σ : Fin 3 → ℤ,
      (∀ i, 0 ≤ σ i ∧ σ i < p i) ∧ τ = normalDegree p b σ ∧
      ∃ M : ℕ, ∀ m ≥ M,
        (Module.finrank ℂ (rootPiece p τ m) : ℚ) =
          (m : ℚ) * rationalDegree p (fun i => by have := hp.1 i; omega) τ + 1 -
            ∑ i, (rootResidue p σ m i : ℚ) / (p i : ℚ) := by
  obtain ⟨b, σ, hσ, rfl⟩ := degree_normal_exists p
    (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ
  exact ⟨b, σ, hσ, rfl, ternary_root_hilbert_eventual_formula p hp ha b σ hτ⟩

end CanonicalRoots
