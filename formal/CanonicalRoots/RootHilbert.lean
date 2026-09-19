import CanonicalRoots.HilbertPieces
import CanonicalRoots.RootArithmetic

noncomputable section
namespace CanonicalRoots

theorem normalDegree_normalize {n : ℕ} (p : Fin n → ℕ) (b : ℤ) (e : Fin n → ℤ) :
    normalDegree p b e = normalDegree p (b + ∑ i, e i / (p i : ℤ))
      (fun i => e i % (p i : ℤ)) := by
  apply (normalDegree_eq_iff p _ _ _ _).mpr
  refine ⟨fun i => e i / (p i : ℤ), by ring, ?_⟩
  intro i
  change e i - e i % (p i : ℤ) = (p i : ℤ) * (e i / (p i : ℤ))
  have h := Int.emod_add_ediv_mul (e i) (p i : ℤ)
  rw [mul_comm] at h
  omega

def rootCarry {n : ℕ} (p : Fin n → ℕ) (b : ℤ) (σ : Fin n → ℤ) (m : ℕ) : ℤ :=
  (m : ℤ) * b + ∑ i, ((m : ℤ) * σ i) / (p i : ℤ)

def rootResidue {n : ℕ} (p : Fin n → ℕ) (σ : Fin n → ℤ) (m : ℕ) (i : Fin n) : ℤ :=
  ((m : ℤ) * σ i) % (p i : ℤ)

theorem rootResidue_bounded {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (σ : Fin n → ℤ) (m : ℕ) (i : Fin n) :
    0 ≤ rootResidue p σ m i ∧ rootResidue p σ m i < p i := by
  have hi : (0 : ℤ) < p i := by exact_mod_cast hp i
  exact ⟨Int.emod_nonneg _ (ne_of_gt hi), Int.emod_lt_of_pos _ hi⟩

theorem rootDegree_normal {n : ℕ} (p : Fin n → ℕ) (b : ℤ) (σ : Fin n → ℤ) (m : ℕ) :
    m • normalDegree p b σ = normalDegree p (rootCarry p b σ m) (rootResidue p σ m) := by
  rw [nsmul_normalDegree]
  exact normalDegree_normalize p _ _

/-- The original paper's piecewise Hilbert formula for every actual root-degree component. -/
theorem rootHilbert_formula {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℤ) (σ : Fin (n + 1) → ℤ) (m : ℕ) :
    Module.finrank ℂ (rootPiece p (normalDegree p b σ) m) =
      normalHilbertCoefficient n (rootCarry p b σ m) :=
  rootPiece_finrank p hp _ m _ _ (rootResidue_bounded p hp σ m) (rootDegree_normal p b σ m)

theorem normalDegree_add_c {n : ℕ} (p : Fin n → ℕ) (b u : ℤ) (e : Fin n → ℤ) :
    normalDegree p (b + u) e = normalDegree p b e + u • cDegree p := by
  simp only [normalDegree_expression, add_zsmul]
  abel

/-- The period and slope follow from equality in the full degree group, including torsion. -/
theorem rootCarry_residue_periodic {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℤ) (σ : Fin n → ℤ) (N m : ℕ) (u : ℤ)
    (hN : N • normalDegree p b σ = u • cDegree p) :
    rootCarry p b σ (m + N) = rootCarry p b σ m + u ∧
      rootResidue p σ (m + N) = rootResidue p σ m := by
  apply degree_normal_unique p hp _ _ _ _ (rootResidue_bounded p hp σ (m + N))
    (rootResidue_bounded p hp σ m)
  rw [← rootDegree_normal, add_nsmul, hN, rootDegree_normal, normalDegree_add_c]

theorem canonicalRootCarry_periodic {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 0 < a) (b : ℤ) (σ : Fin n → ℤ)
    (hroot : IsCanonicalRoot p a (normalDegree p b σ)) (m : ℕ) :
    rootCarry p b σ (m + signatureLcm p) =
        rootCarry p b σ m + signatureIndex p / (a : ℤ) ∧
      rootResidue p σ (m + signatureLcm p) = rootResidue p σ m :=
  rootCarry_residue_periodic p hp b σ _ m _ (canonicalRoot_denominator p hp ha _ hroot)

theorem rationalDegree_normal {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 0)
    (b : ℤ) (e : Fin n → ℤ) :
    rationalDegree p hp (normalDegree p b e) = (b : ℚ) + ∑ i, (e i : ℚ) / (p i : ℚ) := by
  simp [normalDegree_expression, div_eq_mul_inv]

theorem rootCarry_rational {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 0)
    (b : ℤ) (σ : Fin n → ℤ) (m : ℕ) :
    (rootCarry p b σ m : ℚ) = (m : ℚ) * rationalDegree p hp (normalDegree p b σ) -
      ∑ i, (rootResidue p σ m i : ℚ) / (p i : ℚ) := by
  have h := congrArg (rationalDegree p hp) (rootDegree_normal p b σ m)
  simp only [map_nsmul, nsmul_eq_mul, rationalDegree_normal] at h ⊢
  linarith

theorem rootPiece_zero_finrank {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) : Module.finrank ℂ (rootPiece p τ 0) = 1 := by
  have h := rootPiece_finrank p hp τ 0 0 (fun _ => 0)
    (fun i => ⟨le_refl _, by exact_mod_cast hp i⟩)
    (by simp [normalDegree_expression])
  simpa [normalHilbertCoefficient] using h

end CanonicalRoots
