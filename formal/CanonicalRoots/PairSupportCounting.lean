import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

noncomputable section
namespace CanonicalRoots

/-- At least four coordinates cannot be covered on every ordered pair by only
as many supports unless each coordinate has its own singleton support. -/
theorem singleton_supports_of_pair_cover {σ κ : Type*} [Fintype σ] [Fintype κ]
    [DecidableEq σ] (S : κ → Finset σ) (hn : 4 ≤ Fintype.card σ)
    (hc : Fintype.card κ ≤ Fintype.card σ)
    (hcover : ∀ i j : σ, i ≠ j → ∃ k, i ∈ S k ∧ S k ⊆ {i, j}) :
    ∀ i : σ, ∃ k, S k = {i} := by
  classical
  intro i
  by_contra hnone
  push Not at hnone
  let B := {j : σ // j ≠ i}
  have hpair : ∀ j : B, ∃ k, S k = {i, j.val} := by
    intro j
    obtain ⟨k, hi, hk⟩ := hcover i j.val j.property.symm
    have hj : j.val ∈ S k := by
      by_contra hj
      apply hnone k
      apply Finset.Subset.antisymm
      · intro l hl
        have he := hk hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
        exact he.resolve_right (fun h => hj (h ▸ hl))
      · simpa only [Finset.singleton_subset_iff] using hi
    exact ⟨k, Finset.Subset.antisymm hk (by simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro hi hj)⟩
  choose f hf using hpair
  have hfinj : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    have hj : j.val ∈ S (f k) := by rw [← he, hf]; simp
    rw [hf] at hj
    simpa only [Finset.mem_insert, Finset.mem_singleton, j.property, false_or] using hj
  have hcard : Fintype.card B = Fintype.card σ - 1 := by
    simpa only [B, Fintype.card_unique] using Fintype.card_subtype_compl (fun j : σ => j = i)
  have herase : 2 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  obtain ⟨j, k, l, hj, hk, hl, hjk, hjl, hkl⟩ := Finset.two_lt_card_iff.mp herase
  have hji := (Finset.mem_erase.mp hj).1
  have hki := (Finset.mem_erase.mp hk).1
  have hli := (Finset.mem_erase.mp hl).1
  obtain ⟨s, hs, hS⟩ := hcover j k hjk
  obtain ⟨t, ht, hT⟩ := hcover k l hkl
  have hst : s ≠ t := by
    intro he
    have hh := hT (he ▸ hs)
    simp only [Finset.mem_insert, Finset.mem_singleton, hjk, hjl, or_self] at hh
  have hsi : i ∉ S s := by
    intro hi
    have hh := hS hi
    simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hji, Ne.symm hki, or_self] at hh
  have hti : i ∉ S t := by
    intro hi
    have hh := hT hi
    simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hki, Ne.symm hli, or_self] at hh
  let g : Bool → κ := fun b => if b then s else t
  have hginj : Function.Injective g := by
    intro a b he
    cases a <;> cases b <;> simp_all [g]
  have hdisj : ∀ j b, f j ≠ g b := by
    intro j b he
    have hi : i ∈ S (f j) := by rw [hf]; simp
    cases b
    · change f j = t at he
      exact hti (he ▸ hi)
    · change f j = s at he
      exact hsi (he ▸ hi)
  have hbound := Fintype.card_le_of_injective (Sum.elim f g) (hfinj.sumElim hginj hdisj)
  rw [Fintype.card_sum, Fintype.card_bool, hcard] at hbound
  omega

end CanonicalRoots
