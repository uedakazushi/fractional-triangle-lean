import CanonicalRoots.CanonicalFiniteFree

noncomputable section
namespace CanonicalRoots

local instance {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p) (u : ℕ) :
    Fintype (RootBox p τ u) := Fintype.ofFinite _

/-- The degree-m slice of the actual root monomial basis, after division into powers and box. -/
def RootBoxPieceIndex {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u m : ℕ) :=
  {q : (Fin n →₀ ℕ) × RootBox p τ u //
    rootBoxDegree p τ u q.2 + N * ∑ i, q.1 i = m}

section Box
variable {n a : ℕ} (p : Fin (n + 1) → ℕ)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p)

theorem rootPiece_eq_span_box (m : ℕ) :
    rootPiece p τ m = Submodule.span ℂ
      (Set.range (fun q : RootBoxPieceIndex p τ N u m =>
        rootPowerBoxBasis p hp ha τ hτ N u hu hN q.val)) := by
  classical
  apply le_antisymm
  · intro x hx
    have hrepr := (rootPowerBoxBasis p hp ha τ hτ N u hu hN).linearCombination_repr x
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
    have hproject := congrArg (rootProjection p τ m) hrepr
    rw [rootProjection_of_mem p τ (root_multiples_injective p hp ha τ hτ) m m hx,
      ite_eq_left rfl, map_sum] at hproject
    rw [← hproject]
    apply Submodule.sum_mem
    intro q hq
    rw [map_smul, rootProjection_of_mem p τ (root_multiples_injective p hp ha τ hτ)
      m _ (rootPowerBoxBasis_homogeneous p hp ha τ hτ N u hu hN q.1 q.2)]
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨q, h.symm⟩, rfl⟩)
    · simp
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have h := rootPowerBoxBasis_homogeneous p hp ha τ hτ N u hu hN q.val.1 q.val.2
    rwa [q.property] at h

/-- A basis of the actual homogeneous component, rather than a prescribed numerical model. -/
def rootBoxPieceBasis (m : ℕ) :
    Module.Basis (RootBoxPieceIndex p τ N u m) ℂ (rootPiece p τ m) :=
  (Module.Basis.span ((rootPowerBoxBasis p hp ha τ hτ N u hu hN).linearIndependent.comp
    (fun q : RootBoxPieceIndex p τ N u m => q.val) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (rootPiece_eq_span_box p hp ha τ hτ N u hu hN m).symm)

include hp ha hτ hu hN in
theorem rootPiece_finrank_box (m : ℕ) :
    Module.finrank ℂ (rootPiece p τ m) = Nat.card (RootBoxPieceIndex p τ N u m) :=
  Module.finrank_eq_nat_card_basis (rootBoxPieceBasis p hp ha τ hτ N u hu hN m)

end Box

/-- Weak compositions with a fixed offset and a positive common weight. -/
def WeightedCompositions (n N D m : ℕ) :=
  {d : Fin n →₀ ℕ // D + N * ∑ i, d i = m}

def weightedCompositionsEquiv (n N D m : ℕ) (hN : 0 < N)
    (h : D ≤ m ∧ N ∣ m - D) :
    WeightedCompositions n N D m ≃ Sym (Fin n) ((m - D) / N) := by
  have heq : D + N * ((m - D) / N) = m := by
    rw [Nat.mul_div_cancel' h.2]
    omega
  refine (Finsupp.equivFunOnFinite.subtypeEquiv ?_).trans
    (Sym.equivNatSumOfFintype (Fin n) ((m - D) / N)).symm
  intro d
  change (D + N * ∑ i, d i = m) ↔ ∑ i, d i = (m - D) / N
  constructor
  · intro hd
    nlinarith
  · intro hd
    rwa [hd]

/-- The contribution of one homogeneous free generator to a Hilbert coefficient. -/
def weightedCompositionCount (n N D m : ℕ) : ℕ :=
  if D ≤ m ∧ N ∣ m - D then (n + (m - D) / N - 1).choose ((m - D) / N) else 0

theorem weightedCompositions_card (n N D m : ℕ) (hN : 0 < N) :
    Nat.card (WeightedCompositions n N D m) = weightedCompositionCount n N D m := by
  classical
  unfold weightedCompositionCount
  split_ifs with h
  · rw [Nat.card_congr (weightedCompositionsEquiv n N D m hN h), Nat.card_eq_fintype_card,
      Sym.card_sym_eq_choose, Fintype.card_fin]
  · have : IsEmpty (WeightedCompositions n N D m) := ⟨by
      intro d
      apply h
      have hd := d.property
      refine ⟨by omega, ?_⟩
      have heq : m - D = N * ∑ i, d.val i := by omega
      exact ⟨_, heq⟩⟩
    simp

def rootBoxPieceIndexEquivSigma {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u m : ℕ) : RootBoxPieceIndex p τ N u m ≃
      (q : RootBox p τ u) × WeightedCompositions n N (rootBoxDegree p τ u q) m where
  toFun x := ⟨x.val.2, ⟨x.val.1, x.property⟩⟩
  invFun x := ⟨(x.2.val, x.1), x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every Hilbert coefficient of the actual root ring is a finite sum over the root box. -/
theorem rootPiece_finrank_box_sum {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p) (hNpos : 0 < N) (m : ℕ) :
    Module.finrank ℂ (rootPiece p τ m) =
      ∑ q : RootBox p τ u, weightedCompositionCount n N (rootBoxDegree p τ u q) m := by
  classical
  let : Module.Finite ℂ (rootPiece p τ m) :=
    rootPiece_finite p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ m
  let : Finite (RootBoxPieceIndex p τ N u m) :=
    Module.Finite.finite_basis (rootBoxPieceBasis p hp ha τ hτ N u hu hN m)
  let (q : RootBox p τ u) : Finite (WeightedCompositions n N (rootBoxDegree p τ u q) m) :=
    @Finite.of_injective _ (RootBoxPieceIndex p τ N u m) ‹Finite (RootBoxPieceIndex p τ N u m)›
      (fun d => (⟨(d.val, q), d.property⟩ : RootBoxPieceIndex p τ N u m))
      (fun _ _ h => Subtype.ext (congrArg (fun x => x.val.1) h))
  rw [rootPiece_finrank_box p hp ha τ hτ N u hu hN m,
    Nat.card_congr (rootBoxPieceIndexEquivSigma p τ N u m), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun q _ => weightedCompositions_card n N _ m hNpos)

end CanonicalRoots
