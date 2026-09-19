import CanonicalRoots.RootHilbert

noncomputable section
namespace CanonicalRoots

/-- Uniform residue bounds give a lower bound for the carry without asymptotic notation. -/
theorem rootCarry_lower_bound {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℤ) (σ : Fin n → ℤ) (m : ℕ) :
    (m : ℚ) * rationalDegree p (fun i => ne_of_gt (hp i)) (normalDegree p b σ) - n ≤
      (rootCarry p b σ m : ℚ) := by
  rw [rootCarry_rational p (fun i => ne_of_gt (hp i)) b σ m]
  have hsum : (∑ i, (rootResidue p σ m i : ℚ) / (p i : ℚ)) ≤ n := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i _
        apply (div_le_one (by exact_mod_cast hp i)).mpr
        exact_mod_cast (le_of_lt (rootResidue_bounded p hp σ m i).2)
      _ = n := by simp
  linarith

theorem rootCarry_eventually_nonneg {n a : ℕ} (p : Fin n → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (b : ℤ) (σ : Fin n → ℤ)
    (hroot : IsCanonicalRoot p a (normalDegree p b σ)) :
    ∃ M : ℕ, ∀ m ≥ M, 0 ≤ rootCarry p b σ m := by
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  let μ := rationalDegree p (fun i => ne_of_gt (hpos i)) (normalDegree p b σ)
  have hμ : 0 < μ := root_degree_positive p hp ha _ hroot
  obtain ⟨M, hM⟩ := exists_nat_ge ((n : ℚ) / μ)
  refine ⟨M, fun m hm => ?_⟩
  have hbound : (n : ℚ) ≤ (M : ℚ) * μ := (div_le_iff₀ hμ).mp hM
  have hmm : (M : ℚ) ≤ m := by exact_mod_cast hm
  have hlower := rootCarry_lower_bound p hpos b σ m
  change (m : ℚ) * μ - n ≤ (rootCarry p b σ m : ℚ) at hlower
  have hcarry : (0 : ℚ) ≤ rootCarry p b σ m := by nlinarith
  exact_mod_cast hcarry

theorem normalHilbertCoefficient_pos {n : ℕ} (hn : 1 ≤ n) {b : ℤ} (hb : 0 ≤ b) :
    0 < normalHilbertCoefficient n b := by
  rw [normalHilbertCoefficient, ite_eq_right (not_lt_of_ge hb)]
  exact Nat.choose_pos (by omega)

/-- Every sufficiently large degree of the actual root ring is nonzero, with no congruence restriction. -/
theorem rootPiece_eventually_finrank_pos {n a : ℕ} (hn : 1 ≤ n)
    (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    ∃ M : ℕ, ∀ m ≥ M, 0 < Module.finrank ℂ (rootPiece p τ m) := by
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  obtain ⟨b, σ, _hσ, rfl⟩ := degree_normal_exists p hpos τ
  obtain ⟨M, hM⟩ := rootCarry_eventually_nonneg p hp ha b σ hτ
  refine ⟨M, fun m hm => ?_⟩
  rw [rootHilbert_formula p hpos b σ m]
  exact normalHilbertCoefficient_pos hn (hM m hm)

theorem rootPiece_eventually_ne_bot {n a : ℕ} (hn : 1 ≤ n)
    (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    ∃ M : ℕ, ∀ m ≥ M, rootPiece p τ m ≠ ⊥ := by
  obtain ⟨M, hM⟩ := rootPiece_eventually_finrank_pos hn p hp ha τ hτ
  refine ⟨M, fun m hm hbot => ?_⟩
  have h := hM m hm
  rw [hbot] at h
  simp at h

end CanonicalRoots
