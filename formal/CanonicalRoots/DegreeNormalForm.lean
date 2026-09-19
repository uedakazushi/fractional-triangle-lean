import CanonicalRoots.RationalDegree

noncomputable section
namespace CanonicalRoots

/-- The full integer relation lattice; no saturation or rationalization is used. -/
def relationMap {n : ℕ} (p : Fin n → ℕ) : (Fin n → ℤ) →+ FreeDegrees n where
  toFun v k := match k with
    | none => -∑ i, v i
    | some i => (p i : ℤ) * v i
  map_zero' := by ext k; cases k <;> simp
  map_add' v w := by ext k; cases k <;> simp [mul_add, Finset.sum_add_distrib, add_comm]

theorem relationMap_eq_sum {n : ℕ} (p : Fin n → ℕ) (v : Fin n → ℤ) :
    relationMap p v = ∑ i, v i • ((p i : ℤ) • Pi.single (some i) 1 - Pi.single none 1) := by
  classical
  ext k
  cases k with
  | none => simp [relationMap, Finset.sum_neg_distrib]
  | some j => simp [relationMap, Pi.single_apply, eq_comm, mul_comm]

theorem degreeRelations_eq_range {n : ℕ} (p : Fin n → ℕ) :
    degreeRelations p = (relationMap p).range := by
  classical
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [relationMap_eq_sum]
    simp [Pi.single_apply]
  · rintro x ⟨v, rfl⟩
    rw [relationMap_eq_sum]
    apply AddSubgroup.sum_mem
    intro i hi
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _

/-- Equality in the original quotient is exactly membership in the integer relation lattice. -/
theorem degree_eq_iff {n : ℕ} (p : Fin n → ℕ) (u v : FreeDegrees n) :
    QuotientAddGroup.mk' (degreeRelations p) u = QuotientAddGroup.mk' (degreeRelations p) v ↔
    ∃ t : Fin n → ℤ, u none - v none = -∑ i, t i ∧
      ∀ i, u (some i) - v (some i) = (p i : ℤ) * t i := by
  rw [← sub_eq_zero, ← map_sub]
  change (QuotientAddGroup.mk (u - v) : DegreeGroup p) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff, degreeRelations_eq_range]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (congrFun ht none).symm, fun i => (congrFun ht (some i)).symm⟩
  · rintro ⟨t, hc, hx⟩
    refine ⟨t, ?_⟩
    ext k
    cases k with
    | none => exact hc.symm
    | some i => exact (hx i).symm

def normalFree {n : ℕ} (b : ℤ) (e : Fin n → ℤ) : FreeDegrees n :=
  fun k => match k with | none => b | some i => e i

def normalDegree {n : ℕ} (p : Fin n → ℕ) (b : ℤ) (e : Fin n → ℤ) : DegreeGroup p :=
  QuotientAddGroup.mk' (degreeRelations p) (normalFree b e)

theorem normalDegree_expression {n : ℕ} (p : Fin n → ℕ) (b : ℤ) (e : Fin n → ℤ) :
    normalDegree p b e = b • cDegree p + ∑ i, e i • xDegree p i := by
  classical
  have h : normalFree b e = b • Pi.single none 1 + ∑ i, e i • Pi.single (some i) 1 := by
    ext k
    cases k with
    | none => simp [normalFree]
    | some j => simp [normalFree, Pi.single_apply, eq_comm]
  simp [normalDegree, h, cDegree, xDegree]

theorem normalDegree_eq_iff {n : ℕ} (p : Fin n → ℕ) (b c : ℤ) (e f : Fin n → ℤ) :
    normalDegree p b e = normalDegree p c f ↔
    ∃ t : Fin n → ℤ, b - c = -∑ i, t i ∧ ∀ i, e i - f i = (p i : ℤ) * t i :=
  degree_eq_iff p (normalFree b e) (normalFree c f)

/-- Carrying by Euclidean division produces a representative of every actual quotient element. -/
theorem degree_normal_exists {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (l : DegreeGroup p) :
    ∃ b : ℤ, ∃ e : Fin n → ℤ, (∀ i, 0 ≤ e i ∧ e i < p i) ∧ l = normalDegree p b e := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective (degreeRelations p) l
  refine ⟨u none + ∑ i, u (some i) / (p i : ℤ), fun i => u (some i) % (p i : ℤ), ?_, ?_⟩
  · intro i
    have hi : (0 : ℤ) < p i := by exact_mod_cast hp i
    exact ⟨Int.emod_nonneg _ (ne_of_gt hi), Int.emod_lt_of_pos _ hi⟩
  · apply (degree_eq_iff p _ _).mpr
    refine ⟨fun i => u (some i) / (p i : ℤ), ?_, ?_⟩
    · simp [normalFree]
    · intro i
      change u (some i) - u (some i) % (p i : ℤ) = (p i : ℤ) * (u (some i) / (p i : ℤ))
      have h := Int.emod_add_ediv_mul (u (some i)) (p i : ℤ)
      rw [mul_comm] at h
      omega

theorem bounded_residue_unique (p e f t : ℤ) (hp : 0 < p)
    (he : 0 ≤ e ∧ e < p) (hf : 0 ≤ f ∧ f < p) (h : e - f = p * t) : e = f := by
  have ht : t = 0 := by
    by_contra hn
    have : t ≤ -1 ∨ 1 ≤ t := by omega
    rcases this with ht | ht <;> nlinarith
  simp [ht] at h
  exact sub_eq_zero.mp h

/-- Both the carry and every bounded residue are unique, including for groups with torsion. -/
theorem degree_normal_unique {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (b c : ℤ) (e f : Fin n → ℤ)
    (he : ∀ i, 0 ≤ e i ∧ e i < p i) (hf : ∀ i, 0 ≤ f i ∧ f i < p i)
    (h : normalDegree p b e = normalDegree p c f) : b = c ∧ e = f := by
  obtain ⟨t, hc, hx⟩ := (normalDegree_eq_iff p b c e f).mp h
  have hef : e = f := by
    funext i
    exact bounded_residue_unique _ _ _ _ (by exact_mod_cast hp i) (he i) (hf i) (hx i)
  subst f
  have ht : t = 0 := by
    funext i
    have hi : (p i : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (hp i))
    have hz := hx i
    simp only [sub_self] at hz
    exact (mul_eq_zero.mp hz.symm).resolve_left hi
  simp [ht] at hc
  exact ⟨sub_eq_zero.mp hc, rfl⟩

theorem nsmul_normalDegree {n : ℕ} (p : Fin n → ℕ) (a : ℕ) (b : ℤ) (e : Fin n → ℤ) :
    a • normalDegree p b e = normalDegree p ((a : ℤ) * b) (fun i => (a : ℤ) * e i) := by
  unfold normalDegree
  rw [← map_nsmul]
  congr 1
  ext k
  cases k <;> simp [normalFree]

theorem omega_normalDegree {n : ℕ} (p : Fin n → ℕ) :
    omegaDegree p = normalDegree p 1 (fun _ => -1) := by
  simp [normalDegree_expression, omegaDegree, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Exact integer carry equations for roots of omega in L. -/
theorem canonicalRoot_normal_iff {n a : ℕ} (p : Fin n → ℕ) (b : ℤ) (e : Fin n → ℤ) :
    IsCanonicalRoot p a (normalDegree p b e) ↔
      ∃ q : Fin n → ℤ, (a : ℤ) * b + ∑ i, q i = 1 ∧
        ∀ i, (a : ℤ) * e i + 1 = (p i : ℤ) * q i := by
  rw [IsCanonicalRoot, nsmul_normalDegree, omega_normalDegree, normalDegree_eq_iff]
  simp only [sub_neg_eq_add]
  constructor <;> rintro ⟨q, hc, hx⟩ <;> exact ⟨q, by omega, hx⟩

/-- Any actual root forces the root index to be coprime to every signature entry. -/
theorem canonicalRoot_coprime {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (i : Fin n) :
    IsCoprime (a : ℤ) (p i : ℤ) := by
  obtain ⟨b, e, he, rfl⟩ := degree_normal_exists p hp τ
  obtain ⟨q, hc, hx⟩ := (canonicalRoot_normal_iff p b e).mp hτ
  refine ⟨-e i, q i, ?_⟩
  nlinarith [hx i]

/-- Multiplication by an index coprime to every p_i is injective on the entire group L. -/
theorem degree_nsmul_injective {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 0 < a) (hcop : ∀ i, IsCoprime (a : ℤ) (p i : ℤ)) :
    Function.Injective (fun l : DegreeGroup p => a • l) := by
  intro x y hxy
  obtain ⟨b, e, he, rfl⟩ := degree_normal_exists p hp x
  obtain ⟨c, f, hf, rfl⟩ := degree_normal_exists p hp y
  change a • normalDegree p b e = a • normalDegree p c f at hxy
  rw [nsmul_normalDegree, nsmul_normalDegree] at hxy
  obtain ⟨q, hc, hx⟩ := (normalDegree_eq_iff p _ _ _ _).mp hxy
  have hef : e = f := by
    funext i
    have hdiv : (p i : ℤ) ∣ (a : ℤ) * (e i - f i) :=
      ⟨q i, by nlinarith [hx i]⟩
    obtain ⟨t, ht⟩ := (hcop i).symm.dvd_of_dvd_mul_left hdiv
    exact bounded_residue_unique _ _ _ _ (by exact_mod_cast hp i) (he i) (hf i) ht
  subst f
  have hq : q = 0 := by
    funext i
    have hi : (p i : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (hp i))
    have hz := hx i
    simp only [sub_self] at hz
    exact (mul_eq_zero.mp hz.symm).resolve_left hi
  have hbc : b = c := by
    have hapos : (0 : ℤ) < a := by exact_mod_cast ha
    simp [hq] at hc
    nlinarith
  rw [hbc]

/-- If an actual root exists, it is unique. No root-uniqueness assumption is imported. -/
theorem canonicalRoot_unique {n a : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (ha : 0 < a) (τ σ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (hσ : IsCanonicalRoot p a σ) : τ = σ := by
  apply degree_nsmul_injective p hp ha (canonicalRoot_coprime p hp τ hτ)
  exact hτ.trans hσ.symm

end CanonicalRoots
