import CanonicalRoots.CanonicalFiniteFree

noncomputable section
namespace CanonicalRoots

/-- The actual degree quotient governing the finite diagonal action; torsion is retained. -/
abbrev RootDegreeQuotient {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :=
  DegreeGroup p ⧸ AddSubgroup.zmultiples τ

def rootDegreeQuotientMap {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :
    DegreeGroup p →+ RootDegreeQuotient p τ := QuotientAddGroup.mk' _

@[simp] theorem rootDegreeQuotientMap_tau {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :
    rootDegreeQuotientMap p τ τ = 0 := by
  change (QuotientAddGroup.mk τ : RootDegreeQuotient p τ) = 0
  exact (QuotientAddGroup.eq_zero_iff τ).mpr (AddSubgroup.mem_zmultiples τ)

theorem rootDegreeQuotientMap_normal_mod {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (b : ℤ) (σ : Fin n → ℤ) :
    rootDegreeQuotientMap p τ (normalDegree p b σ) =
      rootDegreeQuotientMap p τ (normalDegree p (b % (u : ℤ)) σ) := by
  have hc : (u : ℤ) • rootDegreeQuotientMap p τ (cDegree p) = 0 := by
    have he := congrArg (rootDegreeQuotientMap p τ) hN
    simpa only [map_nsmul, rootDegreeQuotientMap_tau, nsmul_zero, natCast_zsmul] using he.symm
  have hb : b • rootDegreeQuotientMap p τ (cDegree p) =
      (b % (u : ℤ)) • rootDegreeQuotientMap p τ (cDegree p) := by
    have hmul : ((b / (u : ℤ)) * (u : ℤ)) • rootDegreeQuotientMap p τ (cDegree p) =
        (b / (u : ℤ)) • ((u : ℤ) • rootDegreeQuotientMap p τ (cDegree p)) :=
      mul_zsmul (rootDegreeQuotientMap p τ (cDegree p)) (b / (u : ℤ)) (u : ℤ)
    conv_lhs => rw [← Int.emod_add_ediv_mul b (u : ℤ)]
    rw [add_zsmul, hmul, hc, smul_zero]
    exact add_zero ((b % (u : ℤ)) • rootDegreeQuotientMap p τ (cDegree p))
  simp only [normalDegree_expression, map_add, map_zsmul, map_sum, hb]

/-- Every quotient degree has a representative in a finite box of integer normal forms. -/
theorem rootDegreeQuotient_finite_of_denominator {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, 0 < p i) (τ : DegreeGroup p) (N u : ℕ) (hu : 0 < u)
    (hN : N • τ = u • cDegree p) : Finite (RootDegreeQuotient p τ) := by
  let f : (Fin u × (∀ i, Fin (p i))) → RootDegreeQuotient p τ := fun v =>
    rootDegreeQuotientMap p τ (normalDegree p v.1 (fun i => v.2 i))
  apply Finite.of_surjective f
  intro z
  obtain ⟨l, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples τ) z
  obtain ⟨b, σ, hσ, rfl⟩ := degree_normal_exists p hp l
  let v : Fin u × (∀ i, Fin (p i)) :=
    (⟨(b % (u : ℤ)).toNat, by
      have := Int.emod_nonneg b (by omega : (u : ℤ) ≠ 0)
      have := Int.emod_lt_of_pos b (by omega : (0 : ℤ) < u)
      omega⟩, fun i => ⟨(σ i).toNat, by have := hσ i; omega⟩)
  refine ⟨v, ?_⟩
  have hv : (v.1 : ℤ) = b % (u : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg b (by omega))
  have he : (fun i => (v.2 i : ℤ)) = σ :=
    funext (fun i => Int.toNat_of_nonneg (hσ i).1)
  change rootDegreeQuotientMap p τ (normalDegree p (v.1 : ℤ) _) = _
  rw [hv, he]
  exact (rootDegreeQuotientMap_normal_mod p τ N u hN b σ).symm

/-- Finiteness of L/Zτ follows from the actual root equation, with no character or invariant premise. -/
theorem canonicalRootDegreeQuotient_finite {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    Finite (RootDegreeQuotient p τ) :=
  rootDegreeQuotient_finite_of_denominator p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ
    (signatureLcm p) (canonicalRootScale p a) (canonicalRootScale_pos p hp ha τ hτ)
    (canonicalRoot_nat_denominator p hp ha τ hτ)

/-- Complex unit-valued characters of the actual degree quotient. -/
abbrev RootCharacter {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :=
  Multiplicative (RootDegreeQuotient p τ) →* ℂˣ

theorem canonicalRootCharacters_finite {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    Finite (RootCharacter p τ) := by
  let : Finite (RootDegreeQuotient p τ) := canonicalRootDegreeQuotient_finite p hp ha τ hτ
  let : NeZero ((Monoid.exponent (Multiplicative (RootDegreeQuotient p τ)) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast
      (Monoid.exponent_ne_zero_of_finite (G := Multiplicative (RootDegreeQuotient p τ)))⟩
  let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
    (Multiplicative (RootDegreeQuotient p τ)) ℂ).some
  exact Finite.of_injective e e.injective

theorem rootCharacters_separate {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (γ : RootDegreeQuotient p τ) (hγ : γ ≠ 0) :
    ∃ χ : RootCharacter p τ, χ (Multiplicative.ofAdd γ) ≠ 1 := by
  let : Finite (RootDegreeQuotient p τ) := canonicalRootDegreeQuotient_finite p hp ha τ hτ
  let : NeZero ((Monoid.exponent (Multiplicative (RootDegreeQuotient p τ)) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast
      (Monoid.exponent_ne_zero_of_finite (G := Multiplicative (RootDegreeQuotient p τ)))⟩
  exact CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (Multiplicative (RootDegreeQuotient p τ)) ℂ hγ

/-- The characters detect precisely the original integer root line in L. -/
theorem rootCharacters_trivial_iff {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (l : DegreeGroup p) :
    (∀ χ : RootCharacter p τ, χ (Multiplicative.ofAdd (rootDegreeQuotientMap p τ l)) = 1) ↔
      l ∈ AddSubgroup.zmultiples τ := by
  have hz : (∀ χ : RootCharacter p τ, χ (Multiplicative.ofAdd (rootDegreeQuotientMap p τ l)) = 1) ↔
      rootDegreeQuotientMap p τ l = 0 := by
    constructor
    · intro h
      by_contra hn
      obtain ⟨χ, hχ⟩ := rootCharacters_separate p hp ha τ hτ _ hn
      exact hχ (h χ)
    · intro h χ
      rw [h]
      exact χ.map_one
  exact hz.trans (QuotientAddGroup.eq_zero_iff l)

end CanonicalRoots
