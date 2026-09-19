import CanonicalRoots.RootPointOrigin
import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n a : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
/-- Every positive homogeneous root element vanishes at the original root origin. -/
theorem rootOriginPoint_eq_zero_of_positive_piece (m : ℕ) (hm : 0 < m)
    (r : RootRing p τ) (hr : r ∈ rootPiece p τ m) :
    rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ r = 0 := by
  obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp hr
  have hc : f.coeff 0 = 0 := by
    by_contra hn
    have hd : (0 : DegreeGroup p) = m • τ := by
      simpa only [map_zero] using hf hn
    have heq : m = 0 := root_multiples_injective p hp ha τ hτ (hd.symm.trans (zero_nsmul τ).symm)
    omega
  change ambientQuotient p f = (r : AmbientRing p) at he
  change fermatPoint p (fun _ => 0) (by
    apply Finset.sum_eq_zero
    intro i _
    exact zero_pow (by have := hp.1 i; omega)) (r : AmbientRing p) = 0
  rw [← he]
  change aeval (fun _ : Fin n => (0 : ℂ)) f = 0
  simpa only [show (fun _ : Fin n => (0 : ℂ)) = 0 from rfl, aeval_zero,
    Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_eq] using hc

def RootHypersurfacePresentation.polynomialMap (H : RootHypersurfacePresentation p τ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] RootRing p τ :=
  H.graded_equiv.toAlgEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _)

theorem RootHypersurfacePresentation.polynomialMap_surjective
    (H : RootHypersurfacePresentation p τ) : Function.Surjective (H.polynomialMap p τ) :=
  H.graded_equiv.toAlgEquiv.surjective.comp (Ideal.Quotient.mkₐ_surjective ℂ _)

theorem RootHypersurfacePresentation.polynomialMap_relation
    (H : RootHypersurfacePresentation p τ) : H.polynomialMap p τ H.polynomial = 0 := by
  change H.graded_equiv.toAlgEquiv (Ideal.Quotient.mk _ H.polynomial) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]

include hp ha hτ in
theorem RootHypersurfacePresentation.polynomialMap_origin
    (H : RootHypersurfacePresentation p τ) :
    (rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ).comp
      (H.polynomialMap p τ) = aeval (fun _ : Fin n => (0 : ℂ)) := by
  apply MvPolynomial.algHom_ext
  intro i
  change rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ
    (H.polynomialMap p τ (X i)) = aeval (fun _ => (0 : ℂ)) (X i)
  rw [aeval_X]
  apply rootOriginPoint_eq_zero_of_positive_piece p τ hp ha hτ (H.weights i) (H.weights_pos i)
  apply (H.graded_equiv.preserves (H.weights i) _).mp
  exact Submodule.mem_map.mpr ⟨X i, isWeightedHomogeneous_X ℂ H.weights i, rfl⟩

end CanonicalRoots
