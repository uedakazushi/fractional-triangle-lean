import CanonicalRoots.RootMonomialGeneration
import CanonicalRoots.HigherRealization

noncomputable section
open CanonicalRoots

-- Instantiate the generation theorem on an actual realized four-variable root ring.
-- No hypothetical presentation or extra algebra-generation premise occurs in this example.
example : ∃ τ : DegreeGroup ![2,3,7,43], IsCanonicalRoot ![2,3,7,43] 1 τ ∧
    ∃ f : Fin 4 → RootPositiveMonomialIndex ![2,3,7,43] τ,
      Function.Injective f ∧
      Algebra.adjoin ℂ (Set.range (fun i =>
        rootMonomialBasis ![2,3,7,43] (by decide) τ (f i).val)) = ⊤ ∧
      ∀ i, 0 < rootMonomialDegree ![2,3,7,43] τ (f i).val := by
  obtain ⟨τ, hτ, hp, ⟨H⟩⟩ := higher_root_realization (by decide : 0 < 4) ![2,3,7,43]
    (by decide +kernel) (by decide : 0 < 1)
    (by unfold Pairwise; decide +kernel) (by decide +kernel)
  exact ⟨τ, hτ, H.exists_monomial_generators _ (by decide +kernel) τ hp (by decide) hτ⟩

-- The chosen basis lives in the original root-origin cotangent space, not a replacement ring.
example {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p)
    (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (H : RootHypersurfacePresentation p τ) :
    ∃ b : Module.Basis (Fin (n + 1)) ℂ
      (RingHom.ker (rootOriginPoint p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ).toRingHom).Cotangent,
      ∀ i, ∃ q : RootPositiveMonomialIndex p τ,
        b i = rootMonomialCotangent p (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ q := by
  obtain ⟨f, _, b, hb⟩ := H.exists_monomial_cotangent_basis p
    (fun i => lt_of_lt_of_le (by decide) (hp.1 i)) τ hp ha hτ
  exact ⟨b, fun i => ⟨f i, hb i⟩⟩

end
