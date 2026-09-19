import CanonicalRoots.AmbientCharacterAction

noncomputable section
namespace CanonicalRoots

/-- Negative rational degrees vanish in the actual polynomial quotient. -/
theorem ambientPiece_eq_bot_of_rationalDegree_neg {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : ∀ i, 0 < p i) (l : DegreeGroup p)
    (hl : rationalDegree p (fun i => ne_of_gt (hp i)) l < 0) :
    ambientPiece p l = ⊥ := by
  rw [ambientPiece_eq_span p (hp 0)]
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  have h := monomialDegree_nonnegative p hp (q.val.1.cons (q.val.2 : ℕ))
  rw [q.property] at h
  exact False.elim (not_lt_of_ge h hl)

/-- The integer root line has no extra nonzero negative pieces. -/
theorem ambientPiece_le_root_of_mem_zmultiples {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) (l : DegreeGroup p)
    (hl : l ∈ AddSubgroup.zmultiples τ) : ambientPiece p l ≤ rootModule p τ := by
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hl
  by_cases hm : 0 ≤ m
  · have he : m • τ = m.toNat • τ := by
      conv_lhs => rw [← Int.toNat_of_nonneg hm]
      exact natCast_zsmul τ m.toNat
    rw [he]
    exact le_iSup (fun k : ℕ => ambientPiece p (k • τ)) m.toNat
  · have hpos : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
    have ht := root_degree_positive p hp ha τ hτ
    have hneg : rationalDegree p (fun i => ne_of_gt (hpos i)) (m • τ) < 0 := by
      rw [map_zsmul, zsmul_eq_mul]
      exact mul_neg_of_neg_of_pos (by exact_mod_cast (lt_of_not_ge hm)) ht
    rw [ambientPiece_eq_bot_of_rationalDegree_neg p hpos _ hneg]
    exact bot_le

/-- Character separation applied to an actual nonzero homogeneous component. -/
theorem fixed_nonzero_projection_degree {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) {x : AmbientRing p}
    (hx : x ∈ ambientCharacterFixed p τ) (l : DegreeGroup p)
    (hl : ambientProjection p l x ≠ 0) : l ∈ AddSubgroup.zmultiples τ := by
  apply (rootCharacters_trivial_iff p hp ha τ hτ l).mp
  intro χ
  have he := ambientProjection_characterHom p τ χ l x
  rw [hx χ] at he
  have hv : rootCharacterValue p τ χ l = 1 := by
    have hs : (rootCharacterValue p τ χ l - 1) • ambientProjection p l x = 0 := by
      rw [sub_smul, one_smul, ← he, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hl)
  exact Units.ext hv

/-- The root subalgebra is precisely the fixed algebra of the finite character group.
All objects here are the original quotient and subalgebra; no invariant-ring hypothesis is used. -/
theorem rootSubalgebra_eq_characterFixed {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) : rootSubalgebra p τ = ambientCharacterFixed p τ := by
  classical
  let : DecidableEq (DegreeGroup p) := Classical.decEq _
  let : GradedAlgebra (ambientPiece p) := ambientGradedAlgebra p
  apply le_antisymm (rootSubalgebra_le_characterFixed p τ)
  intro x hx
  change x ∈ rootModule p τ
  rw [← DirectSum.sum_support_decompose (ambientPiece p) x]
  apply Submodule.sum_mem
  intro l _
  rw [← ambientProjection_eq_decompose]
  by_cases hl : ambientProjection p l x = 0
  · rw [hl]
    exact Submodule.zero_mem _
  · exact ambientPiece_le_root_of_mem_zmultiples p hp ha τ hτ l
      (fixed_nonzero_projection_degree p hp ha τ hτ hx l hl)
      (ambientProjection_mem p l x)

/-- The fixed-ring identification as a complex algebra equivalence. -/
def rootRingEquivCharacterFixed {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p)
    (hτ : IsCanonicalRoot p a τ) : RootRing p τ ≃ₐ[ℂ] ambientCharacterFixed p τ :=
  Subalgebra.equivOfEq _ _ (rootSubalgebra_eq_characterFixed p hp ha τ hτ)

end CanonicalRoots
