import CanonicalRoots.AmbientPieceBasis
import CanonicalRoots.MonomialNormalForm
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

noncomputable section
namespace CanonicalRoots

theorem pieceIndex_normal_iff {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℤ) (e : Fin (n + 1) → ℤ) (he : ∀ i, 0 ≤ e i ∧ e i < p i)
    (q : (Fin n →₀ ℕ) × Fin (p 0)) :
    Finsupp.weight (xDegree p) (q.1.cons (q.2 : ℕ)) = normalDegree p b e ↔
      (∑ i, (q.1 i / p i.succ : ℕ) : ℤ) = b ∧
      (q.2 : ℤ) = e 0 ∧ ∀ i, (q.1 i % p i.succ : ℕ) = e i.succ := by
  simpa only [Fin.sum_univ_succ, Fin.forall_fin_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    Nat.div_eq_of_lt q.2.isLt, Nat.mod_eq_of_lt q.2.isLt, Int.natCast_zero, zero_add] using
    monomialDegree_eq_normal_iff p hp (q.1.cons (q.2 : ℕ)) b e he

theorem pieceIndex_nat_normal_iff {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℕ) (e : Fin (n + 1) → ℕ) (he : ∀ i, e i < p i)
    (q : (Fin n →₀ ℕ) × Fin (p 0)) :
    Finsupp.weight (xDegree p) (q.1.cons (q.2 : ℕ)) = normalDegree p b (fun i => e i) ↔
      (∑ i, q.1 i / p i.succ) = b ∧
      (q.2 : ℕ) = e 0 ∧ ∀ i, q.1 i % p i.succ = e i.succ := by
  simpa only [← Nat.cast_sum, Int.natCast_inj] using
    pieceIndex_normal_iff p hp b (fun i => e i)
      (fun i => ⟨by positivity, by exact_mod_cast he i⟩) q

/-- Euclidean quotients identify the basis indices with compositions of the carry. -/
def pieceIndexEquivCompositions {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℕ) (e : Fin (n + 1) → ℕ) (he : ∀ i, e i < p i) :
    AmbientPieceIndex p (normalDegree p b (fun i => e i)) ≃
      {v : Fin n → ℕ // ∑ i, v i = b} where
  toFun q := ⟨fun i => q.val.1 i / p i.succ,
    ((pieceIndex_nat_normal_iff p hp b e he q.val).mp q.property).1⟩
  invFun v := ⟨(Finsupp.equivFunOnFinite.symm (fun i => e i.succ + p i.succ * v.val i),
    ⟨e 0, he 0⟩), by
      apply (pieceIndex_nat_normal_iff p hp b e he _).mpr
      constructor
      · simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt (he _), hp] using v.property
      · exact ⟨rfl, fun i => by simp [Nat.add_mod, Nat.mod_eq_of_lt (he i.succ)]⟩⟩
  left_inv q := by
    have h := (pieceIndex_nat_normal_iff p hp b e he q.val).mp q.property
    apply Subtype.ext
    apply Prod.ext
    · ext i
      change e i.succ + p i.succ * (q.val.1 i / p i.succ) = q.val.1 i
      rw [← h.2.2 i]
      exact Nat.mod_add_div _ _
    · apply Fin.ext
      exact h.2.1.symm
  right_inv v := by
    apply Subtype.ext
    funext i
    change (e i.succ + p i.succ * v.val i) / p i.succ = v.val i
    simp [Nat.add_mul_div_left, Nat.div_eq_of_lt (he i.succ), hp]

/-- A finite, explicit basis of every nonnegative normal-form degree. -/
def ambientPieceSymBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℕ) (e : Fin (n + 1) → ℕ) (he : ∀ i, e i < p i) :
    Module.Basis (Sym (Fin n) b) ℂ (ambientPiece p (normalDegree p b (fun i => e i))) :=
  (ambientPieceBasis p (hp 0) _).reindex
    ((pieceIndexEquivCompositions p hp b e he).trans (Sym.equivNatSumOfFintype (Fin n) b).symm)

theorem ambientPiece_finrank_nat {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℕ) (e : Fin (n + 1) → ℕ) (he : ∀ i, e i < p i) :
    Module.finrank ℂ (ambientPiece p (normalDegree p b (fun i => e i))) =
      (n + b - 1).choose b := by
  rw [Module.finrank_eq_card_basis (ambientPieceSymBasis p hp b e he),
    Sym.card_sym_eq_choose, Fintype.card_fin]

theorem ambientPiece_eq_bot_of_negative {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : ∀ i, 0 < p i) (b : ℤ) (e : Fin (n + 1) → ℤ)
    (he : ∀ i, 0 ≤ e i ∧ e i < p i) (hb : b < 0) :
    ambientPiece p (normalDegree p b e) = ⊥ := by
  have hempty : IsEmpty (AmbientPieceIndex p (normalDegree p b e)) := ⟨by
    intro q
    have h := ((pieceIndex_normal_iff p hp b e he q.val).mp q.property).1
    have hnonneg : (0 : ℤ) ≤ b := h ▸ Finset.sum_nonneg (fun i _ => Int.natCast_nonneg _)
    omega⟩
  rw [ambientPiece_eq_span p (hp 0)]
  simp

/-- The Hilbert coefficient dictated by an integral carry, including negative carries. -/
def normalHilbertCoefficient (n : ℕ) (b : ℤ) : ℕ :=
  if b < 0 then 0 else (n + b.toNat - 1).choose b.toNat

theorem ambientPiece_finrank {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (b : ℤ) (e : Fin (n + 1) → ℤ) (he : ∀ i, 0 ≤ e i ∧ e i < p i) :
    Module.finrank ℂ (ambientPiece p (normalDegree p b e)) = normalHilbertCoefficient n b := by
  by_cases hb : b < 0
  · rw [ambientPiece_eq_bot_of_negative p hp b e he hb]
    simp [normalHilbertCoefficient, hb]
  · have heq : (fun i => ((e i).toNat : ℤ)) = e := funext fun i => Int.toNat_of_nonneg (he i).1
    have h := ambientPiece_finrank_nat p hp b.toNat (fun i => (e i).toNat)
      (fun i => by have := he i; omega)
    have hbq : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_not_gt hb)
    rw [hbq, heq] at h
    simpa [normalHilbertCoefficient, hb] using h

theorem ambientPiece_finite {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (l : DegreeGroup p) : Module.Finite ℂ (ambientPiece p l) := by
  obtain ⟨b, e, he, rfl⟩ := degree_normal_exists p hp l
  by_cases hb : b < 0
  · rw [ambientPiece_eq_bot_of_negative p hp b e he hb]
    infer_instance
  · have heq : (fun i => ((e i).toNat : ℤ)) = e := funext fun i => Int.toNat_of_nonneg (he i).1
    have h := Module.Finite.of_basis (ambientPieceSymBasis p hp b.toNat (fun i => (e i).toNat)
      (fun i => by have := he i; omega))
    have hbq : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (le_of_not_gt hb)
    rwa [hbq, heq] at h

theorem rootPiece_finite {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) (m : ℕ) : Module.Finite ℂ (rootPiece p τ m) := by
  let := ambientPiece_finite p hp (m • τ)
  exact Module.Finite.equiv (rootPieceEquivAmbient p τ m).symm

/-- The Hilbert function of the actual root algebra is obtained from the carry in L. -/
theorem rootPiece_finrank {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) (m : ℕ) (b : ℤ) (e : Fin (n + 1) → ℤ)
    (he : ∀ i, 0 ≤ e i ∧ e i < p i) (hdegree : m • τ = normalDegree p b e) :
    Module.finrank ℂ (rootPiece p τ m) = normalHilbertCoefficient n b := by
  rw [(rootPieceEquivAmbient p τ m).finrank_eq, hdegree]
  exact ambientPiece_finrank p hp b e he

end CanonicalRoots
