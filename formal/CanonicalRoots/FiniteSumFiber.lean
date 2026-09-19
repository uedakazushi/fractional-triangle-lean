import CanonicalRoots.RootBox
import Mathlib.Data.ZMod.Basic

noncomputable section
namespace CanonicalRoots

/-- In a vector with a prescribed sum, the first coordinate is uniquely determined by the tail. -/
def sumFiberEquiv {G : Type*} [AddCommGroup G] (n : ℕ) (b : G) :
    {f : Fin (n + 1) → G // ∑ i, f i = b} ≃ (Fin n → G) where
  toFun f := fun i => f.val i.succ
  invFun f := ⟨Fin.cons (b - ∑ i, f i) f, by simp [Fin.sum_univ_succ]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have h := f.property
    rw [Fin.sum_univ_succ] at h
    simp only [Fin.cons_zero]
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm)
  right_inv _ := rfl

def boundedResidueEquiv (u : ℕ) (hu : 0 < u) : Fin u ≃ ZMod u := by
  let : NeZero u := ⟨ne_of_gt hu⟩
  exact {
    toFun := fun i => (i.val : ZMod u)
    invFun := fun x => ⟨x.val, ZMod.val_lt x⟩
    left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
    right_inv := ZMod.natCast_zmod_val }

/-- Bounded integer vectors with one congruence on their sum. -/
def BoundedSumFiber (n u : ℕ) (b : ℤ) :=
  {d : Fin n → Fin u // (u : ℤ) ∣ (∑ i, (d i : ℤ)) - b}

def boundedSumFiberEquiv (n u : ℕ) (hu : 0 < u) (b : ℤ) :
    BoundedSumFiber (n + 1) u b ≃ (Fin n → ZMod u) := by
  let e : (Fin (n + 1) → Fin u) ≃ (Fin (n + 1) → ZMod u) :=
    Equiv.piCongrRight (fun _ => boundedResidueEquiv u hu)
  have hc (d : Fin (n + 1) → Fin u) :
      ((u : ℤ) ∣ (∑ i, (d i : ℤ)) - b) ↔ ∑ i, e d i = (b : ZMod u) := by
    change _ ↔ ∑ i, ((d i : ℕ) : ZMod u) = (b : ZMod u)
    have he : (∑ i, ((d i : ℕ) : ZMod u)) = ((∑ i, (d i : ℤ) : ℤ) : ZMod u) := by
      simp only [Int.cast_sum, Int.cast_natCast]
    rw [he, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact dvd_sub_comm
  exact (e.subtypeEquiv hc).trans (sumFiberEquiv n (b : ZMod u))

theorem boundedSumFiber_card (n u : ℕ) (hu : 0 < u) (b : ℤ) :
    Nat.card (BoundedSumFiber (n + 1) u b) = u ^ n := by
  let : NeZero u := ⟨ne_of_gt hu⟩
  rw [Nat.card_congr (boundedSumFiberEquiv n u hu b), Nat.card_eq_fintype_card]
  simp

end CanonicalRoots
