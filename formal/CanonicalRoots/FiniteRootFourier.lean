import Mathlib.Algebra.Field.GeomSum
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

noncomputable section
namespace CanonicalRoots

/-- A finite algebraic summation identity; no analytic limit or infinite sum is used. -/
theorem weighted_geometric_sum_mul (q : ℂ) (p : ℕ) :
    (1 - q) * (∑ j ∈ Finset.range p, (j : ℂ) * q ^ j) =
      (∑ j ∈ Finset.range p, q ^ j) - 1 - (p - 1 : ℂ) * q ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, pow_succ]
    linear_combination ih

theorem weighted_root_of_unity_sum {p : ℕ} (q : ℂ) (hq : q ^ p = 1) (hne : q ≠ 1) :
    ∑ j ∈ Finset.range p, (j : ℂ) * q ^ j = -(p : ℂ) / (1 - q) := by
  have hs : (∑ j ∈ Finset.range p, q ^ j) = 0 := by
    rw [geom_sum_eq hne, hq]
    simp
  have he := weighted_geometric_sum_mul q p
  rw [hs, hq] at he
  have hn : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  apply (eq_div_iff hn).mpr
  linear_combination he

theorem nontrivial_coprime_root_power {p a : ℕ} (q : ℂ)
    (hq : q ^ p = 1) (hne : q ≠ 1) (hcop : Nat.Coprime p a) : q ^ a ≠ 1 := by
  intro ha
  exact hne ((pow_eq_one_iff_of_coprime hcop).mp ⟨hq, ha⟩)

def residueMultiplicationEquiv {p : ℕ} (hp : 0 < p) (σ t : ℕ)
    (h : σ * t ≡ 1 [MOD p]) : Equiv.Perm (Fin p) where
  toFun j := ⟨(σ * j.val) % p, Nat.mod_lt _ hp⟩
  invFun j := ⟨(t * j.val) % p, Nat.mod_lt _ hp⟩
  left_inv j := by
    apply Fin.ext
    change (t * ((σ * j.val) % p)) % p = j.val
    rw [Nat.mul_mod_mod, ← mul_assoc, mul_comm t σ]
    simpa only [Nat.ModEq, one_mul, Nat.mod_eq_of_lt j.isLt] using (h.mul_right j.val)
  right_inv j := by
    apply Fin.ext
    change (σ * ((t * j.val) % p)) % p = j.val
    rw [Nat.mul_mod_mod, ← mul_assoc]
    simpa only [Nat.ModEq, one_mul, Nat.mod_eq_of_lt j.isLt] using (h.mul_right j.val)

theorem residue_root_power {p σ t : ℕ} (h : σ * t ≡ 1 [MOD p])
    (q : ℂ) (hq : q ^ p = 1) (j : ℕ) :
    (q ^ t) ^ ((σ * j) % p) = q ^ j := by
  rw [← pow_mul]
  apply pow_eq_pow_of_modEq _ hq
  change (t * ((σ * j) % p)) % p = j % p
  rw [Nat.mul_mod_mod, ← mul_assoc, mul_comm t σ]
  simpa only [Nat.ModEq, one_mul] using (h.mul_right j)

/-- The finite Fourier coefficient after the residue permutation. -/
theorem residue_weighted_root_sum {p σ t : ℕ} (hp : 0 < p)
    (h : σ * t ≡ 1 [MOD p]) (q : ℂ) (hq : q ^ p = 1) (hne : q ≠ 1) :
    (∑ j : Fin p, (((σ * j.val) % p : ℕ) : ℂ) * q ^ j.val) =
      -(p : ℂ) / (1 - q ^ t) := by
  have hqt : (q ^ t) ^ p = 1 := by rw [pow_right_comm, hq, one_pow]
  have hqt1 : q ^ t ≠ 1 := by
    intro he
    have hx := residue_root_power h q hq 1
    rw [he, one_pow, pow_one] at hx
    exact hne hx.symm
  let E := residueMultiplicationEquiv hp σ t h
  calc
    _ = ∑ j : Fin p, ((E j).val : ℂ) * (q ^ t) ^ (E j).val := by
      apply Finset.sum_congr rfl
      intro j hj
      change _ = (((σ * j.val) % p : ℕ) : ℂ) * (q ^ t) ^ ((σ * j.val) % p)
      rw [residue_root_power h q hq]
    _ = ∑ j : Fin p, (j.val : ℂ) * (q ^ t) ^ j.val :=
      Equiv.sum_comp E (fun j : Fin p => (j.val : ℂ) * (q ^ t) ^ j.val)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j : ℂ) * (q ^ t) ^ j)]
      exact weighted_root_of_unity_sum _ hqt hqt1

end CanonicalRoots
