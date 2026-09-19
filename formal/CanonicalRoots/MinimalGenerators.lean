import CanonicalRoots.PresentedCotangent

noncomputable section
namespace CanonicalRoots
open MvPolynomial

section Augmented
variable {B : Type*} [CommRing B] [Algebra ℂ B]

theorem cotangent_finrank_le_of_augmented_surjection {m : ℕ}
    (ε : B →ₐ[ℂ] ℂ) (q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] B)
    (hq : Function.Surjective q)
    (hε : ε.comp q = aeval (fun _ : Fin m => (0 : ℂ))) :
    Module.finrank ℂ (RingHom.ker ε.toRingHom).Cotangent ≤ m := by
  have heval (x : MvPolynomial (Fin m) ℂ) : ε (q x) = x.coeff 0 := by
    have h := AlgHom.congr_fun hε x
    simpa [constantCoeff_eq] using h
  have hmap : polynomialOriginIdeal m ≤ (RingHom.ker ε.toRingHom).comap q := by
    intro x hx
    change ε (q x) = 0
    rw [heval]
    exact (mem_polynomialOriginIdeal_iff x).mp hx
  let F := Ideal.mapCotangent (polynomialOriginIdeal m) (RingHom.ker ε.toRingHom) q hmap
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := (RingHom.ker ε.toRingHom).toCotangent_surjective z
    obtain ⟨x, rfl⟩ := hq y
    have hx : x ∈ polynomialOriginIdeal m := by
      rw [mem_polynomialOriginIdeal_iff, ← heval]
      exact hy
    exact ⟨(polynomialOriginIdeal m).toCotangent ⟨x, hx⟩, rfl⟩
  let : FiniteDimensional ℂ (polynomialOriginIdeal m).Cotangent :=
    FiniteDimensional.of_injective (polynomialOriginCotangentEquiv m).toLinearMap
      (polynomialOriginCotangentEquiv m).injective
  simpa [polynomialOriginCotangent_finrank] using
    (LinearMap.finrank_le_finrank_of_surjective hF)

/-- Translating generators by their values at the augmentation preserves generation. -/
theorem cotangent_finrank_le_of_surjection {m : ℕ}
    (ε : B →ₐ[ℂ] ℂ) (q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] B)
    (hq : Function.Surjective q) :
    Module.finrank ℂ (RingHom.ker ε.toRingHom).Cotangent ≤ m := by
  let q₀ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] B :=
    aeval (fun i => q (X i) - algebraMap ℂ B (ε (q (X i))))
  let t : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval (fun i => X i + C (ε (q (X i))))
  have hqt : q₀.comp t = q := by
    ext i
    simp [q₀, t]
  have hq₀ : Function.Surjective q₀ := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨t x, AlgHom.congr_fun hqt x⟩
  apply cotangent_finrank_le_of_augmented_surjection ε q₀ hq₀
  ext i
  simp [q₀]
end Augmented

/-- No algebra presentation of this hypersurface can use fewer than `n` generators.
There is no augmentation-preservation or homogeneity assumption on the other presentation. -/
theorem presented_minimum_generators {n m : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : HasNoConstantOrLinear f) (q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] PresentedRing f)
    (hq : Function.Surjective q) : n ≤ m := by
  have h := cotangent_finrank_le_of_surjection (presentedAugmentation f hf.1) q hq
  rw [← presentedOriginIdeal_eq_ker f hf.1, presentedOriginCotangent_finrank f hf] at h
  exact h

theorem RootHypersurfacePresentation.minimum_generators {n m : ℕ} {p : Fin n → ℕ}
    {τ : DegreeGroup p} (H : RootHypersurfacePresentation p τ)
    (q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] PresentedRing H.polynomial)
    (hq : Function.Surjective q) : n ≤ m :=
  presented_minimum_generators H.polynomial H.no_constant_or_linear q hq

/-- The minimality conclusion holds in the actual canonical-root subalgebra. -/
theorem RootHypersurfacePresentation.root_minimum_generators {n m : ℕ} {p : Fin n → ℕ}
    {τ : DegreeGroup p} (H : RootHypersurfacePresentation p τ)
    (q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] RootRing p τ)
    (hq : Function.Surjective q) : n ≤ m := by
  apply H.minimum_generators (H.graded_equiv.toAlgEquiv.symm.toAlgHom.comp q)
  exact H.graded_equiv.toAlgEquiv.symm.surjective.comp hq

/-- The given `n` generators attain the lower bound. -/
theorem RootHypersurfacePresentation.exists_minimal_surjection {n : ℕ} {p : Fin n → ℕ}
    {τ : DegreeGroup p} (H : RootHypersurfacePresentation p τ) :
    ∃ q : MvPolynomial (Fin n) ℂ →ₐ[ℂ] RootRing p τ, Function.Surjective q := by
  refine ⟨H.graded_equiv.toAlgEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _), ?_⟩
  exact H.graded_equiv.toAlgEquiv.surjective.comp (Ideal.Quotient.mkₐ_surjective ℂ _)

/-- The number of variables in a minimal hypersurface presentation is intrinsic,
even for algebra isomorphisms that do not preserve the chosen gradings. -/
theorem presented_variables_eq_of_algEquiv {n m : ℕ}
    (f : MvPolynomial (Fin n) ℂ) (g : MvPolynomial (Fin m) ℂ)
    (hf : HasNoConstantOrLinear f) (hg : HasNoConstantOrLinear g)
    (e : PresentedRing f ≃ₐ[ℂ] PresentedRing g) : n = m := by
  apply Nat.le_antisymm
  · exact presented_minimum_generators f hf
      (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _))
      (e.symm.surjective.comp (Ideal.Quotient.mkₐ_surjective ℂ _))
  · exact presented_minimum_generators g hg
      (e.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _))
      (e.surjective.comp (Ideal.Quotient.mkₐ_surjective ℂ _))

end CanonicalRoots
