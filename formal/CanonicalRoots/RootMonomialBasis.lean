import CanonicalRoots.RootBox

noncomputable section
namespace CanonicalRoots

def RootMonomialIndex {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) :=
  {q : (Fin n →₀ ℕ) × Fin (p 0) //
    ∃ m : ℕ, Finsupp.weight (xDegree p) (q.1.cons (q.2 : ℕ)) = m • τ}

theorem rootModule_eq_span {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (τ : DegreeGroup p) :
    rootModule p τ = Submodule.span ℂ
      (Set.range (fun q : RootMonomialIndex p τ => ambientMonomialBasis p hp q.val)) := by
  apply le_antisymm
  · apply iSup_le
    intro m
    rw [ambientPiece_eq_span p hp]
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact Submodule.subset_span ⟨⟨q.val, m, q.property⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    obtain ⟨m, hm⟩ := q.property
    apply le_iSup (fun k : ℕ => ambientPiece p (k • τ)) m
    have h := ambientMonomialBasis_homogeneous p hp q.val
    rwa [hm] at h

/-- A complete complex basis of the actual root subalgebra. -/
def rootMonomialBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (τ : DegreeGroup p) : Module.Basis (RootMonomialIndex p τ) ℂ (RootRing p τ) :=
  (Module.Basis.span ((ambientMonomialBasis p hp).linearIndependent.comp
    (fun q : RootMonomialIndex p τ => q.val) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (rootModule_eq_span p hp τ).symm)

@[simp] theorem rootMonomialBasis_apply {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (τ : DegreeGroup p) (q : RootMonomialIndex p τ) :
    (rootMonomialBasis p hp τ q : AmbientRing p) = ambientMonomialBasis p hp q.val := by
  unfold rootMonomialBasis
  erw [Module.Basis.map_apply]
  exact Module.Basis.coe_span_apply _ _

/-- Removing a nonnegative root-degree power from a box expansion stays in the root lattice.
Nonnegativity of the residual monomial degree excludes negative root degrees. -/
theorem box_root_shift_iff {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u k : ℕ) (hN : N • τ = u • cDegree p) (q : AmbientBox p u) :
    (∃ m : ℕ, boxDegree p u q + k • (u • cDegree p) = m • τ) ↔
      ∃ m : ℕ, boxDegree p u q = m • τ := by
  rw [← hN]
  have hmul : k • (N • τ) = (k * N) • τ := by
    rw [← mul_nsmul, Nat.mul_comm]
  rw [hmul]
  constructor
  · rintro ⟨m, hm⟩
    have hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
    have hd := congrArg (rationalDegree p (fun i => ne_of_gt (hpos i))) hm
    simp only [map_add, map_nsmul, nsmul_eq_mul] at hd
    have hnonneg := monomialDegree_nonnegative p hpos (boxExponent p u q)
    change 0 ≤ rationalDegree p _ (boxDegree p u q) at hnonneg
    have hτpos := root_degree_positive p hp ha τ hτ
    have hkm : k * N ≤ m := by
      have : (k * N : ℕ) ≤ (m : ℚ) := by nlinarith
      exact_mod_cast this
    refine ⟨m - k * N, ?_⟩
    apply add_right_cancel (b := (k * N) • τ)
    rw [← add_nsmul, Nat.sub_add_cancel hkm]
    exact hm
  · rintro ⟨m, hm⟩
    exact ⟨m + k * N, by rw [hm, add_nsmul]⟩

def rootPowerBoxIndexEquiv {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p) :
    RootMonomialIndex p τ ≃ (Fin n →₀ ℕ) × RootBox p τ u := by
  let hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  let E := ambientPowerBoxIndexEquiv p hpos u hu
  have hc (q : (Fin n →₀ ℕ) × AmbientBox p u) :
      (∃ m : ℕ, Finsupp.weight (xDegree p) ((E.symm q).1.cons ((E.symm q).2 : ℕ)) = m • τ) ↔
      ∃ m : ℕ, boxDegree p u q.2 = m • τ := by
    change (∃ m : ℕ, Finsupp.weight (xDegree p) ((Finsupp.equivFunOnFinite.symm
      (fun i => (u * p i.succ) * q.1 i + (q.2.1 i : ℕ))).cons (q.2.2 : ℕ)) = m • τ) ↔ _
    rw [powerBoxDegree]
    exact box_root_shift_iff p hp ha τ hτ N u _ hN q.2
  let e1 : RootMonomialIndex p τ ≃
      {q : (Fin n →₀ ℕ) × AmbientBox p u // ∃ m : ℕ, boxDegree p u q.2 = m • τ} :=
    E.subtypeEquiv (by
      intro q
      simpa only [E.symm_apply_apply] using hc (E q))
  exact e1.trans {
    toFun := fun q => (q.val.1, ⟨q.val.2, q.property⟩)
    invFun := fun q => ⟨(q.1, q.2.val), q.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The actual root ring has a basis indexed by a finite root box and polynomial exponents. -/
def rootPowerBoxBasis {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p) :
    Module.Basis ((Fin n →₀ ℕ) × RootBox p τ u) ℂ (RootRing p τ) :=
  (rootMonomialBasis p (lt_of_lt_of_le (by decide) (hp.1 0)) τ).reindex
    (rootPowerBoxIndexEquiv p hp ha τ hτ N u hu hN)

theorem rootPowerBoxBasis_apply {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p)
    (d : Fin n →₀ ℕ) (q : RootBox p τ u) :
    (rootPowerBoxBasis p hp ha τ hτ N u hu hN (d, q) : AmbientRing p) =
      ambientPowerBoxBasis p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) u hu (d, q.val) := by
  rw [rootPowerBoxBasis, Module.Basis.reindex_apply, rootMonomialBasis_apply]
  rw [ambientPowerBoxBasis, Module.Basis.reindex_apply]
  rfl

theorem rootPowerBoxBasis_homogeneous {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p)
    (d : Fin n →₀ ℕ) (q : RootBox p τ u) :
    rootPowerBoxBasis p hp ha τ hτ N u hu hN (d, q) ∈
      rootPiece p τ (rootBoxDegree p τ u q + N * ∑ i, d i) := by
  change (rootPowerBoxBasis p hp ha τ hτ N u hu hN (d, q) : AmbientRing p) ∈
    ambientPiece p ((rootBoxDegree p τ u q + N * ∑ i, d i) • τ)
  rw [rootPowerBoxBasis_apply, ambientPowerBoxBasis_apply]
  apply Submodule.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  apply MvPolynomial.isWeightedHomogeneous_monomial
  rw [powerBoxDegree, rootBoxDegree_spec, ← hN, add_nsmul, mul_nsmul]

theorem canonicalRoot_scale_positive {n a : ℕ} (p : Fin n → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    0 < signatureIndex p / (a : ℤ) := by
  have hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  have h := congrArg (rationalDegree p (fun i => ne_of_gt (hpos i)))
    (canonicalRoot_denominator p hpos (by omega) τ hτ)
  simp only [map_zsmul, rationalDegree_c, zsmul_eq_mul, mul_one] at h
  have hN : (0 : ℚ) < (signatureLcm p : ℤ) := by exact_mod_cast signature_lcm_pos p hpos
  have hμ := root_degree_positive p hp ha τ hτ
  have hu : (0 : ℚ) < (signatureIndex p / (a : ℤ) : ℤ) := h ▸ mul_pos hN hμ
  exact_mod_cast hu

theorem canonicalRoot_nat_denominator {n a : ℕ} (p : Fin n → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    signatureLcm p • τ = (signatureIndex p / (a : ℤ)).toNat • cDegree p := by
  have hu := canonicalRoot_scale_positive p hp ha τ hτ
  have he : ((signatureIndex p / (a : ℤ)).toNat : ℤ) = signatureIndex p / (a : ℤ) :=
    Int.toNat_of_nonneg (le_of_lt hu)
  change (signatureLcm p : ℤ) • τ = ((signatureIndex p / (a : ℤ)).toNat : ℤ) • cDegree p
  rw [he]
  exact canonicalRoot_denominator p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) (by omega) τ hτ

/-- Every admissible actual canonical root has the box basis, without additional lattice premises. -/
def canonicalRootBoxBasis {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    Module.Basis ((Fin n →₀ ℕ) × RootBox p τ ((signatureIndex p / (a : ℤ)).toNat))
      ℂ (RootRing p τ) :=
  rootPowerBoxBasis p hp ha τ hτ (signatureLcm p) _
    (by have := canonicalRoot_scale_positive p hp ha τ hτ; omega)
    (canonicalRoot_nat_denominator p hp ha τ hτ)

end CanonicalRoots
