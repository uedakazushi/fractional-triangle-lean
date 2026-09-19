import CanonicalRoots.RootMonomialOrigin
import CanonicalRoots.RootOriginCotangent
import CanonicalRoots.FiniteSpanningBasis

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i) (τ : DegreeGroup p)

abbrev RootPositiveMonomialIndex := {q : RootMonomialIndex p τ // rootMonomialExponent p τ q ≠ 0}

def rootMonomialCotangent (q : RootPositiveMonomialIndex p τ) :
    (RingHom.ker (rootOriginPoint p hp τ).toRingHom).Cotangent :=
  (RingHom.ker (rootOriginPoint p hp τ).toRingHom).toCotangent
    ⟨rootMonomialBasis p (hp 0) τ q.val, rootMonomialBasis_origin_of_exponent_ne_zero p hp τ q.val q.property⟩

theorem rootMonomialCotangent_eq_projection (q : RootPositiveMonomialIndex p τ) :
    rootMonomialCotangent p hp τ q = augmentationCotangentProjection (rootOriginPoint p hp τ)
      (rootMonomialBasis p (hp 0) τ q.val) := by
  apply congrArg (RingHom.ker (rootOriginPoint p hp τ).toRingHom).toCotangent
  apply Subtype.ext
  rw [augmentationProjection_apply,
    rootMonomialBasis_origin_of_exponent_ne_zero p hp τ q.val q.property, map_zero, sub_zero]

/-- Actual nonconstant monomials can be chosen as a basis of the original root origin cotangent space. -/
theorem RootHypersurfacePresentation.exists_monomial_cotangent_basis {a : ℕ}
    (hpA : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
    (H : RootHypersurfacePresentation p τ) :
    ∃ f : Fin (n + 1) → RootPositiveMonomialIndex p τ, Function.Injective f ∧
      ∃ b : Module.Basis (Fin (n + 1)) ℂ
        (RingHom.ker (rootOriginPoint p hp τ).toRingHom).Cotangent,
        ∀ i, b i = rootMonomialCotangent p hp τ (f i) := by
  classical
  let ε := rootOriginPoint p hp τ
  let I := RingHom.ker ε.toRingHom
  let : FiniteDimensional ℂ I.Cotangent :=
    FiniteDimensional.of_injective (H.rootOriginCotangentEquiv p τ hpA ha hτ).toLinearMap
      (H.rootOriginCotangentEquiv p τ hpA ha hτ).injective
  obtain ⟨f, hf, b, hb⟩ := finite_basis_selected_from_spanning
    (fun q => augmentationCotangentProjection ε (rootMonomialBasis p (hp 0) τ q))
    (augmentationCotangentBasisImage_span ε (rootMonomialBasis p (hp 0) τ))
    (H.rootOriginCotangent_finrank p τ hpA ha hτ)
  have hfpos (i : Fin (n + 1)) : rootMonomialExponent p τ (f i) ≠ 0 := by
    apply rootMonomial_nonzero_cotangent_exponent p hp τ
    rw [← hb]
    exact b.ne_zero i
  refine ⟨fun i => ⟨f i, hfpos i⟩, ?_, b, ?_⟩
  · intro i j he
    exact hf (congrArg Subtype.val he)
  · intro i
    rw [rootMonomialCotangent_eq_projection]
    exact hb i

end CanonicalRoots
