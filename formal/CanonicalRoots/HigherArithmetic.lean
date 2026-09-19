import CanonicalRoots.Candidates

namespace CanonicalRoots

def intProduct (ps : List ℕ) : ℤ := (ps.map Int.ofNat).prod

/-- Sum of products with one coordinate omitted, avoiding integer division. -/
def cofactorSum : List ℕ → ℤ
  | [] => 0
  | q :: ps => intProduct ps + (q : ℤ)*cofactorSum ps

@[simp] theorem intProduct_nil : intProduct [] = 1 := rfl
@[simp] theorem intProduct_cons (q : ℕ) (ps : List ℕ) :
    intProduct (q::ps) = q*intProduct ps := rfl

theorem intProduct_pos (ps : List ℕ) (hp : ∀ p ∈ ps, 1 ≤ p) : 1 ≤ intProduct ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hpi : (1 : ℤ) ≤ p := by exact_mod_cast hp p (by simp)
    have htail := ih (fun q hq => hp q (by simp [hq]))
    simp only [intProduct_cons]
    nlinarith

theorem coordinate_le_product (q : ℕ) (ps : List ℕ) (hp : ∀ p ∈ ps, 1 ≤ p) :
    (q : ℤ) ≤ intProduct (q::ps) := by
  have h := intProduct_pos ps hp
  simp only [intProduct_cons]
  nlinarith

theorem cofactorSum_nonneg (ps : List ℕ) (hp : ∀ p ∈ ps, 1 ≤ p) :
    0 ≤ cofactorSum ps := by
  induction ps with
  | nil => simp [cofactorSum]
  | cons q ps ih =>
    have htail : ∀ p ∈ ps, 1 ≤ p := fun p h => hp p (by simp [h])
    have h := ih htail
    have hprod := intProduct_pos ps htail
    simp only [cofactorSum]
    positivity

/-- Each deleted-factor term is at most the full product divided by the lower bound. -/
theorem cofactor_bound (q : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, 1 ≤ p ∧ q ≤ p) :
    (q : ℤ) * cofactorSum ps ≤ (ps.length : ℤ)*intProduct ps := by
  induction ps with
  | nil => simp [cofactorSum]
  | cons p ps ih =>
    have hp0 := hp p (by simp)
    have htail : ∀ r ∈ ps, 1 ≤ r ∧ q ≤ r := fun r h => hp r (by simp [h])
    have h := ih htail
    have hprod := intProduct_pos ps (fun r hr => (htail r hr).1)
    have hpq : (q : ℤ) ≤ p := by exact_mod_cast hp0.2
    have hmul := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg p)
    have hqp := mul_le_mul_of_nonneg_right hpq (show 0 ≤ intProduct ps by omega)
    simp only [cofactorSum, intProduct_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The exact prefix update preserves the equation for any proposed completion. -/
theorem completion_step (q : ℕ) (ps : List ℕ) (P A a : ℤ) :
    A * intProduct (q::ps) = a + P*cofactorSum (q::ps) ↔
    (A*q-P)*intProduct ps = a + (P*q)*cofactorSum ps := by
  simp only [intProduct_cons, cofactorSum]
  constructor <;> intro h <;> nlinarith [h]

/-- A valid completion has a positive next defect. -/
theorem next_defect_positive (q : ℕ) (ps : List ℕ) (P A a : ℤ)
    (hP : 0 < P) (ha : 0 < a) (hp : ∀ p ∈ ps, 1 ≤ p)
    (he : A * intProduct (q::ps) = a + P*cofactorSum (q::ps)) :
    0 < A*q-P := by
  have h := (completion_step q ps P A a).mp he
  have hprod := intProduct_pos ps hp
  have hcof := cofactorSum_nonneg ps hp
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hright : 0 < a + P*q*cofactorSum ps := by positivity
  nlinarith

/-- The required floor bound, independent of the search implementation. -/
theorem next_coordinate_bound (q : ℕ) (ps : List ℕ) (P A a : ℤ)
    (hP : 0 < P) (hA : 0 < A) (ha : 0 ≤ a) (hq : 1 ≤ q)
    (hp : ∀ p ∈ ps, 1 ≤ p ∧ q ≤ p)
    (he : A * intProduct (q::ps) = a + P*cofactorSum (q::ps)) :
    (q : ℤ) ≤ (((ps.length+1 : ℕ) : ℤ)+a)*P/A := by
  let S := intProduct (q::ps)
  have hprod : 1 ≤ S := intProduct_pos (q::ps) (by
    intro p h
    rcases List.mem_cons.mp h with rfl | h
    · exact hq
    · exact (hp p h).1)
  have hcof := cofactor_bound q (q::ps) (by
    intro p h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨hq,le_rfl⟩
    · exact hp p h)
  have hqS : (q : ℤ) ≤ S := coordinate_le_product q ps (fun p h => (hp p h).1)
  have hPS : (q : ℤ) ≤ P*S := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hPS ha
  have hcscale := mul_le_mul_of_nonneg_left hcof (show 0 ≤ P by omega)
  have heq := congrArg (fun x : ℤ => x * q) he
  have hbound : A*q ≤ (((ps.length+1 : ℕ) : ℤ)+a)*P := by
    simp only [List.length_cons] at hcscale
    change A * S = a + P * cofactorSum (q::ps) at he
    change A * S * q = (a + P * cofactorSum (q::ps))*q at heq
    nlinarith
  exact (Int.le_ediv_iff_mul_le hA).mpr (by nlinarith [hbound])

/-- Exact last coordinate: both divisibility and uniqueness. -/
theorem last_coordinate (q P A a : ℤ) (hA : 0 < A) :
    A*q-P=a ↔ A ∣ (a+P) ∧ q=(a+P)/A := by
  constructor
  · intro h
    have he : a+P=A*q := by omega
    exact ⟨⟨q,he⟩,by rw [he, Int.mul_ediv_cancel_left _ (ne_of_gt hA)]⟩
  · rintro ⟨hd,rfl⟩
    have h := Int.mul_ediv_cancel' hd
    omega

/-- Every returned row satisfies the exact completion equation; no cutoff is assumed. -/
theorem higherSearch_equation (a k : ℕ) (pref : List ℕ) (P A : ℤ) (out : List ℕ)
    (hm : out ∈ higherSearch a k pref P A) :
    ∃ tail : List ℕ, out = pref ++ tail ∧ tail.length = k ∧
      A * intProduct tail = (a : ℤ) + P * cofactorSum tail := by
  induction k generalizing pref P A out with
  | zero =>
    by_cases h : 0 < P ∧ A = a
    · simp only [higherSearch, if_pos h, List.mem_singleton] at hm
      subst out
      exact ⟨[],by simp, rfl, by simp [cofactorSum, h.2]⟩
    · simp [higherSearch, h] at hm
  | succ k ih =>
    by_cases hPA : 0 < P ∧ 0 < A
    · by_cases hk : k = 0
      · subst k
        simp only [higherSearch, if_pos hPA, ↓reduceIte] at hm
        split_ifs at hm with hl
        · simp only [List.mem_singleton] at hm
          let q : ℤ := ((a : ℤ)+P)/A
          have hq : 0 ≤ q := by
            have hlo : (0 : ℤ) ≤ (pref.getLast?.getD 1 + 1 : ℕ) := by positivity
            exact le_trans hlo hl.2.1
          refine ⟨[q.toNat],hm,rfl,?_⟩
          simp only [intProduct_cons, intProduct_nil, cofactorSum, mul_one, mul_zero, add_zero]
          rw [Int.toNat_of_nonneg hq]
          exact Int.mul_ediv_cancel' hl.1
        · simp at hm
      · simp only [higherSearch, if_pos hPA, if_neg hk] at hm
        obtain ⟨q,hq,ho⟩ := List.mem_flatMap.mp hm
        obtain ⟨tail,ht,hk',he⟩ := ih (pref ++ [q]) (P*(q : ℤ)) (A*(q : ℤ)-P) out ho
        refine ⟨q::tail,?_,by simp [hk'],?_⟩
        · simpa [List.append_assoc] using ht
        · exact (completion_step q tail P A a).mpr he
    · simp [higherSearch, hPA] at hm

/-- Soundness of the integer defect equation at the initial state. -/
theorem enumerateHigherCandidates_equation (n a : ℕ) (ps : List ℕ)
    (hm : ps ∈ enumerateHigherCandidates n a) :
    ps.length = n ∧ intProduct ps - cofactorSum ps = a := by
  obtain ⟨tail,ht,hlen,he⟩ := higherSearch_equation a n [] 1 1 ps hm
  simp only [List.nil_append] at ht
  subst ps
  constructor
  · exact hlen
  · simp only [one_mul] at he
    omega

/-- Unbounded order/coprimality condition on a continuation, independent of enumeration. -/
def TailCompatible (pref : List ℕ) : List ℕ → Prop
  | [] => True
  | q::ps => pref.getLast?.getD 1 + 1 ≤ q ∧
      (∀ t ∈ pref, Nat.Coprime q t) ∧ TailCompatible (pref ++ [q]) ps

theorem compatible_lower (pref ps : List ℕ) (hc : TailCompatible pref ps) :
    ∀ q ∈ ps, pref.getLast?.getD 1 + 1 ≤ q := by
  induction ps generalizing pref with
  | nil => simp
  | cons r ps ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hc.1
    · have h := ih (pref ++ [r]) hc.2.2 q hq
      have hr : (pref ++ [r]).getLast?.getD 1 = r := by simp
      rw [hr] at h
      have hc0 := hc.1
      omega

/-- Completeness of the structural recursion for the independent integer continuation condition. -/
theorem higherSearch_complete (a : ℕ) (ha : 0 < a) (pref ps : List ℕ) (P A : ℤ)
    (hP : 0 < P) (hA : 0 < A) (hlo : 2 ≤ pref.getLast?.getD 1 + 1)
    (hc : TailCompatible pref ps)
    (he : A * intProduct ps = (a : ℤ) + P * cofactorSum ps) :
    pref ++ ps ∈ higherSearch a ps.length pref P A := by
  induction ps generalizing pref P A with
  | nil =>
    have h : A = a := by simpa [cofactorSum] using he
    simp [higherSearch, hP, h]
  | cons q ps ih =>
    have hq : 2 ≤ q := le_trans hlo hc.1
    have htail : ∀ r ∈ ps, 1 ≤ r ∧ q ≤ r := by
      intro r hr
      have h := compatible_lower (pref ++ [q]) ps hc.2.2 r hr
      have hlast : (pref ++ [q]).getLast?.getD 1 = q := by simp
      rw [hlast] at h
      constructor <;> omega
    have hqP : 0 < P*(q : ℤ) := by positivity
    have hnext := next_defect_positive q ps P A a hP (by exact_mod_cast ha)
      (fun r hr => (htail r hr).1) he
    have hPA : 0 < P ∧ 0 < A := ⟨hP,hA⟩
    have hgcd : pref.all (fun t => Nat.Coprime q t) = true := by
      simpa using hc.2.1
    cases ps with
    | nil =>
      have heq : A*(q : ℤ)-(P : ℤ)=a := by simpa [cofactorSum] using (by
        nlinarith [he] : A * intProduct [q] - P * cofactorSum [q] = (a : ℤ))
      obtain ⟨hd,hdiv⟩ := (last_coordinate q P A a hA).mp heq
      have hqnat : (((a : ℤ)+P)/A).toNat = q := by rw [← hdiv]; simp
      have hlow : (pref.getLast?.getD 1 + 1 : ℤ) ≤ ((a : ℤ)+P)/A := by
        rw [← hdiv]
        exact_mod_cast hc.1
      simp only [List.length_cons, List.length_nil, higherSearch, if_pos hPA, ↓reduceIte]
      simp [hd, hlow, hqnat, hgcd]
    | cons r ps =>
      have hlen : (r::ps).length ≠ 0 := by simp
      have hb := next_coordinate_bound q (r::ps) P A a hP hA (by positivity)
        (by omega) htail he
      have hbNat : q ≤ ((((r::ps).length+1+a : ℕ) : ℤ)*P/A).toNat := by
        apply Int.ofNat_le.mp
        have ht : (0 : ℤ) ≤ (((((r::ps).length+1+a : ℕ) : ℤ)*P/A)) := by
          push_cast
          exact le_trans (Int.natCast_nonneg q) hb
        rw [Int.toNat_of_nonneg ht]
        push_cast at *
        exact hb
      change pref ++ (q::r::ps) ∈ higherSearch a ((r::ps).length+1) pref P A
      rw [higherSearch, if_pos hPA, if_neg hlen]
      apply List.mem_flatMap.mpr
      refine ⟨q, ?_, ?_⟩
      · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨by simpa using Nat.lt_succ_of_le hbNat, hc.1, hgcd⟩
      · have hrec := ih (pref ++ [q]) (P*(q : ℤ)) (A*(q : ℤ)-P) hqP hnext
          (by simpa using (by omega : 2 ≤ q+1)) hc.2.2
          ((completion_step q (r::ps) P A a).mp he)
        simpa [List.append_assoc] using hrec

/-- General integer completeness at the root state, with no external cutoff. -/
theorem enumerateHigherCandidates_complete (a : ℕ) (ha : 0 < a) (ps : List ℕ)
    (hc : TailCompatible [] ps) (he : intProduct ps - cofactorSum ps = a) :
    ps ∈ enumerateHigherCandidates ps.length a := by
  have h := higherSearch_complete a ha [] ps 1 1 (by norm_num) (by norm_num)
    (by simp) hc (by nlinarith [he])
  simpa [enumerateHigherCandidates] using h

/-- Every returned continuation respects order and all prefix gcd tests. -/
theorem higherSearch_compatible (a k : ℕ) (pref : List ℕ) (P A : ℤ) (out : List ℕ)
    (hm : out ∈ higherSearch a k pref P A) :
    ∃ tail : List ℕ, out = pref ++ tail ∧ TailCompatible pref tail := by
  induction k generalizing pref P A out with
  | zero =>
    by_cases h : 0 < P ∧ A = a
    · simp only [higherSearch, if_pos h, List.mem_singleton] at hm
      subst out
      exact ⟨[],by simp, trivial⟩
    · simp [higherSearch, h] at hm
  | succ k ih =>
    by_cases hPA : 0 < P ∧ 0 < A
    · by_cases hk : k = 0
      · subst k
        simp only [higherSearch, if_pos hPA, ↓reduceIte] at hm
        split_ifs at hm with hl
        · simp only [List.mem_singleton] at hm
          let q : ℤ := ((a : ℤ)+P)/A
          have hq : 0 ≤ q := le_trans (by positivity) hl.2.1
          refine ⟨[q.toNat],hm,?_,?_,trivial⟩
          · have h := hl.2.1
            have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
            change (pref.getLast?.getD 1 + 1 : ℤ) ≤ q at h
            rw [← he] at h
            exact_mod_cast h
          · simpa using hl.2.2
        · simp at hm
      · simp only [higherSearch, if_pos hPA, if_neg hk] at hm
        obtain ⟨q,hq,ho⟩ := List.mem_flatMap.mp hm
        simp only [List.mem_filter, decide_eq_true_eq] at hq
        obtain ⟨tail,ht,hc⟩ := ih (pref ++ [q]) (P*(q : ℤ)) (A*(q : ℤ)-P) out ho
        refine ⟨q::tail,by simpa [List.append_assoc] using ht,hq.2.1,?_,hc⟩
        simpa using hq.2.2
    · simp [higherSearch, hPA] at hm

theorem compatible_coprime_pref (pref ps : List ℕ) (hc : TailCompatible pref ps) :
    ∀ q ∈ ps, ∀ t ∈ pref, Nat.Coprime q t := by
  induction ps generalizing pref with
  | nil => simp
  | cons r ps ih =>
    intro q hq t ht
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hc.2.1 t ht
    · exact ih (pref ++ [r]) hc.2.2 q hq t (by simp [ht])

theorem compatible_pairwise (pref ps : List ℕ) (hc : TailCompatible pref ps) :
    ps.Pairwise (· < ·) ∧ ps.Pairwise Nat.Coprime := by
  induction ps generalizing pref with
  | nil => simp
  | cons q ps ih =>
    obtain ⟨hord,hcop⟩ := ih (pref ++ [q]) hc.2.2
    constructor
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hord⟩
      intro r hr
      have h := compatible_lower (pref ++ [q]) ps hc.2.2 r hr
      simpa using h
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hcop⟩
      intro r hr
      exact (compatible_coprime_pref (pref ++ [q]) ps hc.2.2 r hr q (by simp)).symm

theorem compatible_of_conditions (pref ps : List ℕ)
    (hlo : ∀ q ∈ ps, pref.getLast?.getD 1 + 1 ≤ q)
    (hcross : ∀ q ∈ ps, ∀ t ∈ pref, Nat.Coprime q t)
    (hord : ps.Pairwise (· < ·)) (hcop : ps.Pairwise Nat.Coprime) :
    TailCompatible pref ps := by
  induction ps generalizing pref with
  | nil => trivial
  | cons q ps ih =>
    obtain ⟨hqh,hord'⟩ := List.pairwise_cons.mp hord
    obtain ⟨hqc,hcop'⟩ := List.pairwise_cons.mp hcop
    refine ⟨hlo q (by simp),hcross q (by simp),ih (pref ++ [q]) ?_ ?_ hord' hcop'⟩
    · intro r hr
      simpa using hqh r hr
    · intro r hr t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hcross r (by simp [hr]) t ht
      · simp only [List.mem_singleton] at ht
        subst t
        exact (hqc r hr).symm

theorem compatible_empty_iff (ps : List ℕ) :
    TailCompatible [] ps ↔ (∀ p ∈ ps, 2 ≤ p) ∧
      ps.Pairwise (· < ·) ∧ ps.Pairwise Nat.Coprime := by
  constructor
  · intro hc
    exact ⟨by simpa using compatible_lower [] ps hc,compatible_pairwise [] ps hc⟩
  · rintro ⟨hp,ho,hc⟩
    exact compatible_of_conditions [] ps (by simpa using hp) (by simp) ho hc

/-- Independent higher-dimensional integer signature predicate. -/
def ArithmeticHigher (n a : ℕ) (ps : List ℕ) : Prop :=
  ps.length = n ∧ (∀ p ∈ ps, 2 ≤ p) ∧ ps.Pairwise (· < ·) ∧
    ps.Pairwise Nat.Coprime ∧ intProduct ps - cofactorSum ps = a

/-- All-input arithmetic correctness; no ring-theoretic classification is assumed or asserted. -/
theorem enumerateHigherCandidates_iff (n a : ℕ) (ha : 0 < a) (ps : List ℕ) :
    ps ∈ enumerateHigherCandidates n a ↔ ArithmeticHigher n a ps := by
  constructor
  · intro hm
    obtain ⟨hlen,heq⟩ := enumerateHigherCandidates_equation n a ps hm
    obtain ⟨tail,ht,hc⟩ := higherSearch_compatible a n [] 1 1 ps hm
    simp only [List.nil_append] at ht
    subst tail
    obtain ⟨hp,ho,hc⟩ := (compatible_empty_iff ps).mp hc
    exact ⟨hlen,hp,ho,hc,heq⟩
  · rintro ⟨hlen,hp,ho,hc,he⟩
    have h := enumerateHigherCandidates_complete a ha ps
      ((compatible_empty_iff ps).mpr ⟨hp,ho,hc⟩) he
    simpa [hlen] using h

end CanonicalRoots
