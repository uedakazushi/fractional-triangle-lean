import CanonicalRoots.RationalDegree

noncomputable section
namespace CanonicalRoots
open MvPolynomial

local instance {n : ℕ} (p : Fin n → ℕ) : DecidableEq (DegreeGroup p) := Classical.decEq _
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem fermat_group_homogeneous {n : ℕ} (p : Fin n → ℕ) :
    IsWeightedHomogeneous (xDegree p) (fermat p) (cDegree p) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  have h := (isWeightedHomogeneous_X ℂ (xDegree p) i).pow (p i)
  have he : p i • xDegree p i = cDegree p := degree_relation p i
  rwa [he] at h

theorem fermatIdeal_homogeneous {n : ℕ} (p : Fin n → ℕ) :
    (fermatIdeal p).IsHomogeneous (weightedHomogeneousSubmodule ℂ (xDegree p)) := by
  apply Ideal.homogeneous_span
  intro f hf
  obtain rfl := Set.mem_singleton_iff.mp hf
  exact ⟨cDegree p, fermat_group_homogeneous p⟩

theorem component_mem_fermatIdeal {n : ℕ} (p : Fin n → ℕ)
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ fermatIdeal p) (l : DegreeGroup p) :
    weightedHomogeneousComponent (xDegree p) l f ∈ fermatIdeal p :=
  weightedHomogeneousComponent_mem_of_mem ℂ (xDegree p) (fermatIdeal_homogeneous p) hf l

/-- Homogeneous projection descends to the actual Fermat quotient. -/
def ambientProjection {n : ℕ} (p : Fin n → ℕ) (l : DegreeGroup p) :
    AmbientRing p →ₗ[ℂ] AmbientRing p :=
  ((fermatIdeal p).restrictScalars ℂ).liftQ
    ((ambientQuotient p).toLinearMap.comp (weightedHomogeneousComponent (xDegree p) l)) (by
      intro f hf
      change ambientQuotient p (weightedHomogeneousComponent (xDegree p) l f) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (component_mem_fermatIdeal p hf l))

@[simp] theorem ambientProjection_quotient {n : ℕ} (p : Fin n → ℕ)
    (l : DegreeGroup p) (f : MvPolynomial (Fin n) ℂ) :
    ambientProjection p l (ambientQuotient p f) =
      ambientQuotient p (weightedHomogeneousComponent (xDegree p) l f) := rfl

theorem ambientProjection_mem {n : ℕ} (p : Fin n → ℕ) (l : DegreeGroup p)
    (x : AmbientRing p) : ambientProjection p l x ∈ ambientPiece p l := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (fermatIdeal p) x
  exact Submodule.mem_map.mpr ⟨_, weightedHomogeneousComponent_mem _ _ _, rfl⟩

theorem ambientProjection_of_mem {n : ℕ} (p : Fin n → ℕ) (l k : DegreeGroup p)
    {x : AmbientRing p} (hx : x ∈ ambientPiece p k) :
    ambientProjection p l x = if l = k then x else 0 := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  change ambientProjection p l (ambientQuotient p f) = if l = k then ambientQuotient p f else 0
  rw [ambientProjection_quotient, weightedHomogeneousComponent_of_mem hf]
  split_ifs <;> simp

theorem ambientProjection_eq_self {n : ℕ} (p : Fin n → ℕ) (l : DegreeGroup p)
    {x : AmbientRing p} (hx : x ∈ ambientPiece p l) : ambientProjection p l x = x := by
  simpa using ambientProjection_of_mem p l l hx

/-- A family with mutually annihilating projections is an independent family of submodules. -/
theorem independent_of_projections {ι M : Type*} [AddCommGroup M] [Module ℂ M]
    (S : ι → Submodule ℂ M) (π : ι → M →ₗ[ℂ] M)
    (hsame : ∀ i x, x ∈ S i → π i x = x)
    (hother : ∀ i j, i ≠ j → ∀ x, x ∈ S j → π i x = 0) : iSupIndep S := by
  rw [iSupIndep_def]
  intro i
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  have hker : (⨆ (j) (_ : j ≠ i), S j) ≤ LinearMap.ker (π i) := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hji y hy
    exact hother i j hji.symm y hy
  exact (hsame i x hx).symm.trans (hker hy)

theorem ambientPieces_independent {n : ℕ} (p : Fin n → ℕ) : iSupIndep (ambientPiece p) := by
  apply independent_of_projections (ambientPiece p) (ambientProjection p)
  · intro l x hx
    exact ambientProjection_eq_self p l hx
  · intro l k hlk x hx
    simpa [hlk] using ambientProjection_of_mem p l k hx

theorem ambientPieces_span {n : ℕ} (p : Fin n → ℕ) : (⨆ l, ambientPiece p l) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (fermatIdeal p) x
  have hsum := sum_weightedHomogeneousComponent (xDegree p) f
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)] at hsum
  change ambientQuotient p f ∈ ⨆ l, ambientPiece p l
  rw [← hsum, map_sum]
  apply Submodule.sum_mem
  intro l hl
  exact (le_iSup (ambientPiece p) l) (Submodule.mem_map.mpr
    ⟨_, weightedHomogeneousComponent_mem _ _ _, rfl⟩)

/-- The actual quotient is the internal direct sum of its group-degree pieces. -/
theorem ambientPieces_internal {n : ℕ} (p : Fin n → ℕ) :
    DirectSum.IsInternal (ambientPiece p) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (ambientPieces_independent p) (ambientPieces_span p)

@[instance_reducible] def ambientGradedAlgebra {n : ℕ} (p : Fin n → ℕ) : GradedAlgebra (ambientPiece p) where
  toDecomposition := (ambientPieces_internal p).chooseDecomposition
  toGradedMonoid := {
    one_mem := by
      apply Submodule.mem_map.mpr
      exact ⟨1, isWeightedHomogeneous_one ℂ (xDegree p), (ambientQuotient p).map_one⟩
    mul_mem := fun _ _ _ _ hx hy => ambientPiece_mul p hx hy }

/-- The root ring inherits the projection onto each natural root degree. -/
def rootProjection {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (m : ℕ) :
    RootRing p τ →ₗ[ℂ] RootRing p τ where
  toFun x := ⟨ambientProjection p (m • τ) x,
    (le_iSup (fun k : ℕ => ambientPiece p (k • τ)) m) (ambientProjection_mem p (m • τ) x)⟩
  map_add' x y := by apply Subtype.ext; exact (ambientProjection p (m • τ)).map_add x y
  map_smul' r x := by apply Subtype.ext; exact (ambientProjection p (m • τ)).map_smul r x

theorem rootProjection_of_mem {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (hinj : Function.Injective (fun m : ℕ => m • τ)) (m k : ℕ)
    {x : RootRing p τ} (hx : x ∈ rootPiece p τ k) :
    rootProjection p τ m x = if m = k then x else 0 := by
  apply Subtype.ext
  have h := ambientProjection_of_mem p (m • τ) (k • τ) hx
  change ambientProjection p (m • τ) (x : AmbientRing p) =
    if m • τ = k • τ then (x : AmbientRing p) else 0 at h
  change ambientProjection p (m • τ) x = _
  rw [h]
  simp only [hinj.eq_iff]
  split_ifs <;> rfl

theorem rootPieces_independent {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (hinj : Function.Injective (fun m : ℕ => m • τ)) : iSupIndep (rootPiece p τ) := by
  apply independent_of_projections (rootPiece p τ) (rootProjection p τ)
  · intro m x hx
    simpa using rootProjection_of_mem p τ hinj m m hx
  · intro m k hmk x hx
    simpa [hmk] using rootProjection_of_mem p τ hinj m k hx

theorem rootPieces_span {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :
    (⨆ m, rootPiece p τ m) = ⊤ := by
  have hrange : LinearMap.range (rootSubalgebra p τ).val.toLinearMap = rootModule p τ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have h := Submodule.biSup_comap_eq_top_of_range_eq_biSup
    (Set.univ : Set ℕ) ⟨0, Set.mem_univ 0⟩
    (fun m : ℕ => ambientPiece p (m • τ)) (rootSubalgebra p τ).val.toLinearMap
    (by simpa [rootModule] using hrange)
  simpa [rootPiece] using h

/-- The root algebra is the internal direct sum in the original definition of R. -/
theorem rootPieces_internal {n a : ℕ} (p : Fin n → ℕ) (hp : AdmissibleSignature p)
    (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) :
    DirectSum.IsInternal (rootPiece p τ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (rootPieces_independent p τ (root_multiples_injective p hp ha τ hτ)) (rootPieces_span p τ)

@[instance_reducible] def rootGradedAlgebra {n a : ℕ} (p : Fin n → ℕ) (hp : AdmissibleSignature p)
    (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) : GradedAlgebra (rootPiece p τ) where
  toDecomposition := (rootPieces_internal p hp ha τ hτ).chooseDecomposition
  toGradedMonoid := {
    one_mem := by
      change (1 : AmbientRing p) ∈ ambientPiece p (0 • τ)
      simp only [zero_smul]
      exact Submodule.mem_map.mpr ⟨1, isWeightedHomogeneous_one ℂ (xDegree p), (ambientQuotient p).map_one⟩
    mul_mem := by
      intro i j x y hx hy
      change (x : AmbientRing p) * (y : AmbientRing p) ∈ ambientPiece p ((i + j) • τ)
      rw [add_nsmul]
      exact ambientPiece_mul p hx hy }

end CanonicalRoots
