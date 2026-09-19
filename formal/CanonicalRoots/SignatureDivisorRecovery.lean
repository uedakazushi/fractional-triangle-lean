import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

noncomputable section
namespace CanonicalRoots

def multipleSum (f : ℕ →₀ ℚ) (e : ℕ) : ℚ :=
  f.sum fun r c => if e ∣ r then c else 0

theorem multipleSum_sub (f g : ℕ →₀ ℚ) (e : ℕ) :
    multipleSum (f - g) e = multipleSum f e - multipleSum g e := by
  apply Finsupp.sum_sub_index
  intro r c d
  split_ifs <;> simp

/-- A finitely supported function above one is recovered from its sums over multiples.
The largest element of the difference support isolates its own coefficient. -/
theorem finsupp_eq_of_multipleSum (f g : ℕ →₀ ℚ)
    (hsmall : ∀ r < 2, f r = g r)
    (h : ∀ e, 2 ≤ e → multipleSum f e = multipleSum g e) : f = g := by
  classical
  by_contra hfg
  let d := f - g
  have hd : d ≠ 0 := sub_ne_zero.mpr hfg
  have hs : d.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun he => hd (Finsupp.support_eq_empty.mp he))
  let e := d.support.max' hs
  have hem : e ∈ d.support := Finset.max'_mem _ hs
  have he : 2 ≤ e := by
    by_contra he
    have hz : d e = 0 := sub_eq_zero.mpr (hsmall e (by omega))
    exact (Finsupp.mem_support_iff.mp hem) hz
  have hsum : multipleSum d e = d e := by
    change d.sum (fun r c => if e ∣ r then c else 0) = d e
    have ht := Finsupp.sum_eq_single e
      (f := d) (g := fun r c => if e ∣ r then c else 0)
      (fun r hr hre => ?_) (fun _ => by simp)
    · simpa using ht
    · by_cases hdiv : e ∣ r
      · have hr0 : 0 < r := by
          by_contra hr0
          have : r = 0 := by omega
          subst r
          exact hr (sub_eq_zero.mpr (hsmall 0 (by decide)))
        have hle : r ≤ e := Finset.le_max' _ r (Finsupp.mem_support_iff.mpr hr)
        exact False.elim (hre (le_antisymm hle (Nat.le_of_dvd hr0 hdiv)))
      · simp [hdiv]
  have hz : multipleSum d e = 0 := by
    rw [multipleSum_sub, h e he, sub_self]
  exact (Finsupp.mem_support_iff.mp hem) (hsum.symm.trans hz)

/-- Multiplicities divided by the corresponding order, retaining repetitions. -/
def signatureMultiplicity (s : Multiset ℕ) : ℕ →₀ ℚ :=
  Finsupp.onFinset s.toFinset (fun r => (s.count r : ℚ) / r) (by
    intro r hr
    by_contra hm
    have hz : s.count r = 0 := Multiset.count_eq_zero.mpr (by simpa using hm)
    exact hr (by simp [hz]))

theorem signatureMultiplicity_apply (s : Multiset ℕ) (r : ℕ) :
    signatureMultiplicity s r = (s.count r : ℚ) / r := rfl

def signatureDivisorProfile (s : Multiset ℕ) (e : ℕ) : ℚ :=
  multipleSum (signatureMultiplicity s) e

theorem signatureDivisorProfile_eq_sum (s : Multiset ℕ) (e : ℕ) :
    signatureDivisorProfile s e = (s.map (fun r => if e ∣ r then (r : ℚ)⁻¹ else 0)).sum := by
  unfold signatureDivisorProfile multipleSum signatureMultiplicity
  rw [Finsupp.onFinset_sum _ (fun _ => by simp)]
  rw [Finset.sum_multiset_map_count]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp [div_eq_mul_inv]

/-- The weighted divisor data used in the pole formula determines the full multiset. -/
theorem signature_eq_of_divisorProfile (s t : Multiset ℕ)
    (hs : ∀ r ∈ s, 2 ≤ r) (ht : ∀ r ∈ t, 2 ≤ r)
    (h : ∀ e, 2 ≤ e → signatureDivisorProfile s e = signatureDivisorProfile t e) : s = t := by
  have he : signatureMultiplicity s = signatureMultiplicity t := by
    apply finsupp_eq_of_multipleSum _ _ _ h
    intro r hr
    have hs0 : s.count r = 0 := Multiset.count_eq_zero.mpr (fun hm => by have := hs r hm; omega)
    have ht0 : t.count r = 0 := Multiset.count_eq_zero.mpr (fun hm => by have := ht r hm; omega)
    simp [signatureMultiplicity_apply, hs0, ht0]
  apply Multiset.ext.mpr
  intro r
  by_cases hr : r < 2
  · have hs0 : s.count r = 0 := Multiset.count_eq_zero.mpr (fun hm => by have := hs r hm; omega)
    have ht0 : t.count r = 0 := Multiset.count_eq_zero.mpr (fun hm => by have := ht r hm; omega)
    omega
  · have hn : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    have hc := DFunLike.congr_fun he r
    simp only [signatureMultiplicity_apply] at hc
    exact_mod_cast (div_left_inj' hn).mp hc

end CanonicalRoots
