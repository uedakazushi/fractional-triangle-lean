import CanonicalRoots.RootMonomialCotangentBasis
import CanonicalRoots.RootConnectedGrading
import CanonicalRoots.GradedCotangentGeneration

noncomputable section
namespace CanonicalRoots

variable {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i) (τ : DegreeGroup p)

def rootMonomialDegree (q : RootMonomialIndex p τ) : ℕ := q.property.choose

theorem rootMonomialDegree_spec (q : RootMonomialIndex p τ) :
    Finsupp.weight (xDegree p) (rootMonomialExponent p τ q) =
      rootMonomialDegree p τ q • τ := q.property.choose_spec

theorem rootMonomialBasis_homogeneous (q : RootMonomialIndex p τ) :
    rootMonomialBasis p (hp 0) τ q ∈ rootPiece p τ (rootMonomialDegree p τ q) := by
  change (rootMonomialBasis p (hp 0) τ q : AmbientRing p) ∈
    ambientPiece p (rootMonomialDegree p τ q • τ)
  rw [rootMonomialBasis_apply, ← rootMonomialDegree_spec]
  exact ambientMonomialBasis_homogeneous p (hp 0) q.val

include hp in
theorem rootMonomialDegree_pos (q : RootPositiveMonomialIndex p τ) :
    0 < rootMonomialDegree p τ q.val := by
  by_contra hn
  have hd : rootMonomialDegree p τ q.val = 0 := by omega
  have hm := rootMonomialBasis_homogeneous p hp τ q.val
  rw [hd] at hm
  have he := rootPiece_zero_eq_scalar p hp τ _ hm
  rw [rootMonomialBasis_origin_of_exponent_ne_zero p hp τ q.val q.property, map_zero] at he
  exact (rootMonomialBasis p (hp 0) τ).ne_zero q.val he

/-- A minimal hypersurface presentation yields exactly `n+1` actual nonconstant
monomials generating the original root algebra. No generation assumption is added. -/
theorem RootHypersurfacePresentation.exists_monomial_generators {a : ℕ}
    (hpA : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
    (H : RootHypersurfacePresentation p τ) :
    ∃ f : Fin (n + 1) → RootPositiveMonomialIndex p τ, Function.Injective f ∧
      Algebra.adjoin ℂ (Set.range (fun i => rootMonomialBasis p (hp 0) τ (f i).val)) = ⊤ ∧
      ∀ i, 0 < rootMonomialDegree p τ (f i).val := by
  classical
  let := rootGradedAlgebra p hpA ha τ hτ
  obtain ⟨f, hf, b, hb⟩ := H.exists_monomial_cotangent_basis p hp τ hpA ha hτ
  refine ⟨f, hf, ?_, fun i => rootMonomialDegree_pos p hp τ (f i)⟩
  let ε := rootOriginPoint p hp τ
  let I := RingHom.ker ε.toRingHom
  let x : Fin (n + 1) → I := fun i => ⟨rootMonomialBasis p (hp 0) τ (f i).val,
    rootMonomialBasis_origin_of_exponent_ne_zero p hp τ (f i).val (f i).property⟩
  have he : (fun i => I.toCotangent (x i)) = b := funext fun i => (hb i).symm
  have hs : Submodule.span ℂ (Set.range (fun i => I.toCotangent (x i))) = ⊤ := by
    rw [he, b.span_eq]
  exact graded_adjoin_eq_top_of_cotangent_span (rootPiece p τ) ε
    (rootGradedProjection_zero p hp τ hpA ha hτ) x
    (fun i => ⟨rootMonomialDegree p τ (f i).val, rootMonomialBasis_homogeneous p hp τ (f i).val⟩) hs

end CanonicalRoots
