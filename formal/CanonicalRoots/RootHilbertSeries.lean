import CanonicalRoots.RootBoxHilbert
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section
namespace CanonicalRoots

local instance {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    Fintype (RootBox p τ u) := Fintype.ofFinite _

/-- The Hilbert series is defined from dimensions of the actual homogeneous subspaces. -/
def rootHilbertSeries {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) : PowerSeries ℚ :=
  PowerSeries.mk (fun m => (Module.finrank ℂ (rootPiece p τ m) : ℚ))

/-- The finite box numerator, viewed as a formal power series. -/
def rootBoxNumerator {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    PowerSeries ℚ := ∑ q : RootBox p τ u, PowerSeries.X ^ rootBoxDegree p τ u q

theorem invOneSubPow_coeff (n k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOneSubPow ℚ n).val = ((n + k - 1).choose k : ℚ) := by
  cases n with
  | zero =>
    cases k with
    | zero => simp [PowerSeries.invOneSubPow]
    | succ k => simp [PowerSeries.invOneSubPow]
  | succ n =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
    congr 1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.choose_symm_add : (n + k).choose n = (n + k).choose k)

theorem weightedCompositionCount_coeff (n N D m : ℕ) (hN : 0 < N) :
    PowerSeries.coeff m (PowerSeries.X ^ D *
      PowerSeries.expand N (ne_of_gt hN) (PowerSeries.invOneSubPow ℚ n).val) =
      (weightedCompositionCount n N D m : ℚ) := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hD : D ≤ m
  · rw [ite_eq_left hD, PowerSeries.coeff_expand, invOneSubPow_coeff]
    by_cases hd : N ∣ m - D <;> simp [weightedCompositionCount, hD, hd]
  · simp [weightedCompositionCount, hD]

section Root
variable {n a : ℕ} (p : Fin (n + 1) → ℕ)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p) (hNpos : 0 < N)

include hp ha hτ hu hN in
theorem rootHilbertSeries_eq_box :
    rootHilbertSeries p τ = rootBoxNumerator p τ u *
      PowerSeries.expand N (ne_of_gt hNpos) (PowerSeries.invOneSubPow ℚ n).val := by
  classical
  apply PowerSeries.ext
  intro m
  rw [rootHilbertSeries, PowerSeries.coeff_mk,
    rootPiece_finrank_box_sum p hp ha τ hτ N u hu hN hNpos m]
  simp only [rootBoxNumerator, Finset.sum_mul, map_sum, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun q _ => (weightedCompositionCount_coeff n N _ m hNpos).symm)

include hp ha hτ hu hN hNpos in
/-- An identity of actual formal power series: the Hilbert series has the finite box numerator. -/
theorem rootHilbertSeries_mul_denominator :
    rootHilbertSeries p τ * (1 - PowerSeries.X ^ N) ^ n = rootBoxNumerator p τ u := by
  rw [rootHilbertSeries_eq_box p hp ha τ hτ N u hu hN hNpos, mul_assoc]
  have h := congrArg (PowerSeries.expand N (ne_of_gt hNpos)) (PowerSeries.invOneSubPow ℚ n).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at h
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.expand_X] at h
  rw [h, mul_one]

end Root

theorem canonicalRootHilbertSeries_mul_denominator {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    rootHilbertSeries p τ * (1 - PowerSeries.X ^ signatureLcm p) ^ n =
      rootBoxNumerator p τ (canonicalRootScale p a) :=
  rootHilbertSeries_mul_denominator p hp ha τ hτ (signatureLcm p) (canonicalRootScale p a)
    (canonicalRootScale_pos p hp ha τ hτ) (canonicalRoot_nat_denominator p hp ha τ hτ)
    (signature_lcm_pos p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)))

end CanonicalRoots
