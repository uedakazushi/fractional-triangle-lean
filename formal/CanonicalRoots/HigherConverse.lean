import CanonicalRoots.RootPureSupport
import CanonicalRoots.HigherPurePowerGeneration
import CanonicalRoots.HigherCoprimality

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p)
  (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
/-- The actual isolated hypersurface condition, with no classification premise,
forces the maximal canonical-root scale in at least four variables. -/
theorem RootHypersurfacePresentation.higher_scale_eq_one
    (H : RootHypersurfacePresentation p τ) (hn : 3 ≤ n) :
    canonicalRootScale p a = 1 := by
  have hcop := H.pairwise_coprime p τ hp ha hτ hn
  exact higher_scale_eq_one_of_pure_power_generation p hp ha τ hτ hcop hn
    (H.pure_power_generation p hp ha τ hτ hcop hn)

include hp ha hτ in
theorem RootHypersurfacePresentation.higher_product_defect
    (H : RootHypersurfacePresentation p τ) (hn : 3 ≤ n) :
    ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a := by
  have hcop := H.pairwise_coprime p τ hp ha hτ hn
  have hu := H.higher_scale_eq_one p hp ha τ hτ hn
  have he := congrArg (productDegree p) hτ
  change productDegree p (a • τ) = productDegree p (omegaDegree p) at he
  rw [map_nsmul, productDegree_canonicalRoot p hp ha τ hτ hcop, hu,
    Nat.cast_one, nsmul_eq_mul, mul_one, productDegree_omega] at he
  simpa only [Nat.cast_prod] using he.symm

include hp ha hτ in
theorem RootHypersurfacePresentation.higher_root_eq_top
    (H : RootHypersurfacePresentation p τ) (hn : 3 ≤ n) : rootSubalgebra p τ = ⊤ :=
  CanonicalRoots.higher_root_eq_top p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) ha
    (H.pairwise_coprime p τ hp ha hτ hn) (H.higher_product_defect p hp ha τ hτ hn) τ hτ

include hp ha hτ in
/-- The complete higher-dimensional hypersurface criterion for an actual canonical root.
Its statement is independent of candidate enumeration. -/
theorem higher_root_hypersurface_iff (hn : 3 ≤ n) :
    Nonempty (RootHypersurfacePresentation p τ) ↔
      Pairwise (fun i j => Nat.Coprime (p i) (p j)) ∧
        ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.pairwise_coprime p τ hp ha hτ hn, H.higher_product_defect p hp ha τ hτ hn⟩
  · rintro ⟨hcop, hdefect⟩
    exact ⟨higherRootPresentation (by omega) p hp.1 ha hcop hdefect τ hτ⟩

theorem Target.higher_product_defect (t : Target (n + 1) a) (hn : 3 ≤ n) :
    ((∏ i, t.signature i : ℕ) : ℤ) - ∑ i, (productWeights t.signature i : ℤ) = a :=
  t.presentation.higher_product_defect t.signature t.admissible t.parameter_input
    t.tau t.root_equation hn

/-- Exact existence criterion for signatures of actual higher-dimensional Targets. -/
theorem higher_signature_target_iff (hn : 3 ≤ n) (hp2 : ∀ i, 2 ≤ p i) (ha : 1 ≤ a) :
    (∃ t : Target (n + 1) a, t.signature = p) ↔
      Pairwise (fun i j => Nat.Coprime (p i) (p j)) ∧
        ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.pairwise_coprime hn, t.higher_product_defect hn⟩
  · rintro ⟨hcop, hdefect⟩
    obtain ⟨τ, hτ, hp, ⟨H⟩⟩ := higher_root_realization (by omega) p hp2 ha hcop hdefect
    exact ⟨⟨by omega, ha, p, hp, τ, hτ, H⟩, rfl⟩

end CanonicalRoots
