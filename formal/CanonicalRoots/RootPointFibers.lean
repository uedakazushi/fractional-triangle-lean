import CanonicalRoots.InvariantExtension
import CanonicalRoots.RootPointLocalMap

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p)
  (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ in
/-- Two actual complex points have the same root image precisely when a root
character carries one evaluation map to the other. -/
theorem rootPoint_eq_iff_character (z w : AmbientRing p →ₐ[ℂ] ℂ) :
    rootPoint p τ z = rootPoint p τ w ↔
      ∃ χ : RootCharacter p τ, z = w.comp (ambientCharacterHom p τ χ) := by
  constructor
  · intro hz
    have hker : (RingHom.ker z.toRingHom).under (RootRing p τ) =
        (RingHom.ker w.toRingHom).under (RootRing p τ) := by
      ext r
      change z (r : AmbientRing p) = 0 ↔ w (r : AmbientRing p) = 0
      exact (AlgHom.congr_fun hz r).congr (Eq.refl 0)
    obtain ⟨χ, hχ⟩ := ambient_primes_over_root_transitive p hp ha τ hτ
      (RingHom.ker z.toRingHom) (RingHom.ker w.toRingHom) hker
    refine ⟨χ, AlgHom.ext fun r => ?_⟩
    have hr : r - algebraMap ℂ (AmbientRing p) (z r) ∈ RingHom.ker z.toRingHom := by
      change z (r - algebraMap ℂ (AmbientRing p) (z r)) = 0
      simp
    have hh := Ideal.mem_map_of_mem (ambientCharacterHom p τ χ).toRingHom hr
    rw [← hχ] at hh
    change w (ambientCharacterHom p τ χ (r - algebraMap ℂ (AmbientRing p) (z r))) = 0 at hh
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at hh
    exact (sub_eq_zero.mp hh).symm
  · rintro ⟨χ, rfl⟩
    apply AlgHom.ext
    intro r
    change w (ambientCharacterHom p τ χ (r : AmbientRing p)) = w (r : AmbientRing p)
    rw [rootSubalgebra_le_characterFixed p τ r.property χ]

include hp ha hτ in
/-- Equality in the finite quotient forces a common multiplier on all Fermat powers. -/
theorem rootPoint_eq_powers_proportional (z w : AmbientRing p →ₐ[ℂ] ℂ)
    (hz : rootPoint p τ z = rootPoint p τ w) :
    ∃ ρ : ℂ, ∀ i, z (ambientQuotient p (MvPolynomial.X i)) ^ p i =
      ρ * w (ambientQuotient p (MvPolynomial.X i)) ^ p i := by
  obtain ⟨χ, hχ⟩ := (rootPoint_eq_iff_character p hp ha τ hτ z w).mp hz
  refine ⟨((rootCharacterDegree p τ χ (cDegree p)).toMul : ℂ), fun i => ?_⟩
  have hi := congrArg (fun η : ℂˣ => (η : ℂ))
    ((rootCharacter_coordinate_equations p hp ha τ hτ χ).1 i)
  change rootCharacterValue p τ χ (xDegree p i) ^ p i =
    ((rootCharacterDegree p τ χ (cDegree p)).toMul : ℂ) at hi
  rw [hχ, AlgHom.comp_apply, ambientCharacterHom_X, map_smul, smul_eq_mul, mul_pow, hi]

end CanonicalRoots
