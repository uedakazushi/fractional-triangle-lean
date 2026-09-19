import CanonicalRoots.HigherArithmetic
import Mathlib.Data.List.Nodup

namespace CanonicalRoots

theorem higherSearch_distinct_prefix_disjoint (a k : ℕ) (pref : List ℕ) (q r : ℕ)
    (hq : q ≠ r) (P Q A B : ℤ) :
    List.Disjoint (higherSearch a k (pref ++ [q]) P A) (higherSearch a k (pref ++ [r]) Q B) := by
  apply List.disjoint_left.mpr
  intro ps hps hps'
  obtain ⟨s, hs, _⟩ := higherSearch_compatible a k (pref ++ [q]) P A ps hps
  obtain ⟨t, ht, _⟩ := higherSearch_compatible a k (pref ++ [r]) Q B ps hps'
  have he : pref ++ (q :: s) = pref ++ (r :: t) := by
    simpa only [List.append_assoc, List.singleton_append] using hs.symm.trans ht
  exact hq (List.cons.inj (List.append_cancel_left he)).1

/-- Different recursive choices remain distinguishable in their output prefixes. -/
theorem higherSearch_nodup (a k : ℕ) (pref : List ℕ) (P A : ℤ) :
    (higherSearch a k pref P A).Nodup := by
  induction k generalizing pref P A with
  | zero => simp only [higherSearch]; split_ifs <;> simp
  | succ k ih =>
    by_cases hPA : 0 < P ∧ 0 < A
    · by_cases hk : k = 0
      · subst k
        simp only [higherSearch, ite_eq_left hPA, ↓reduceIte]
        split_ifs <;> simp
      · rw [higherSearch, ite_eq_left hPA, ite_eq_right hk]
        apply List.nodup_flatMap.mpr
        constructor
        · intro q hq
          exact ih _ _ _
        · apply (List.nodup_range.filter _).imp
          intro q r hqr
          exact higherSearch_distinct_prefix_disjoint a k pref q r hqr _ _ _ _
    · simp [higherSearch, hPA]

theorem enumerateHigherCandidates_nodup (n a : ℕ) : (enumerateHigherCandidates n a).Nodup :=
  higherSearch_nodup a n [] 1 1

end CanonicalRoots
