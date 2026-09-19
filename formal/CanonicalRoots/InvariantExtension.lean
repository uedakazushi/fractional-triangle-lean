import CanonicalRoots.RootInvariants

noncomputable section
namespace CanonicalRoots

/-- Register the proved automorphism action for mathlib's invariant-extension API. -/
@[instance_reducible] def rootCharacterMulSemiringAction {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :
    MulSemiringAction (RootCharacter p τ) (AmbientRing p) where
  smul χ x := ambientCharacterHom p τ χ x
  smul_zero χ := map_zero (ambientCharacterHom p τ χ)
  smul_add χ := map_add (ambientCharacterHom p τ χ)
  smul_one χ := map_one (ambientCharacterHom p τ χ)
  smul_mul χ := map_mul (ambientCharacterHom p τ χ)
  one_smul x := DFunLike.congr_fun (ambientCharacterHom_one p τ) x
  mul_smul χ ψ x := DFunLike.congr_fun (ambientCharacterHom_mul p τ χ ψ) x

section Extension
variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
  (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
local instance : MulSemiringAction (RootCharacter p τ) (AmbientRing p) :=
  rootCharacterMulSemiringAction p τ

local instance rootCharacter_smulCommClass :
    SMulCommClass (RootCharacter p τ) (RootRing p τ) (AmbientRing p) where
  smul_comm χ r x := by
    change ambientCharacterHom p τ χ ((r : AmbientRing p) * x) =
      (r : AmbientRing p) * ambientCharacterHom p τ χ x
    rw [map_mul, rootSubalgebra_le_characterFixed p τ r.property χ]

include hp ha hτ

/-- `IsInvariant` is proved from the fixed-ring theorem, never imposed as a new assumption. -/
theorem canonicalRoot_isInvariant :
    Algebra.IsInvariant (RootRing p τ) (AmbientRing p) (RootCharacter p τ) where
  isInvariant x hx := by
    have hxR : x ∈ rootSubalgebra p τ := by
      rw [rootSubalgebra_eq_characterFixed p hp ha τ hτ]
      exact hx
    exact ⟨⟨x, hxR⟩, rfl⟩

/-- The entire Fermat quotient is integral over the actual root ring. -/
theorem ambient_integral_over_root : Algebra.IsIntegral (RootRing p τ) (AmbientRing p) := by
  let : Finite (RootCharacter p τ) := canonicalRootCharacters_finite p hp ha τ hτ
  let : Algebra.IsInvariant (RootRing p τ) (AmbientRing p) (RootCharacter p τ) :=
    canonicalRoot_isInvariant p hp ha τ hτ
  exact Algebra.IsInvariant.isIntegral (RootRing p τ) (AmbientRing p) (RootCharacter p τ)

/-- The quotient morphism Spec T → Spec R is finite. -/
theorem ambient_finite_over_root : Module.Finite (RootRing p τ) (AmbientRing p) := by
  let : Algebra.IsIntegral (RootRing p τ) (AmbientRing p) := ambient_integral_over_root p hp ha τ hτ
  let : Algebra.FiniteType ℂ (AmbientRing p) := inferInstance
  let : Algebra.FiniteType (RootRing p τ) (AmbientRing p) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (RootRing p τ) (AmbientRing p)
  exact Algebra.IsIntegral.finite (R := RootRing p τ) (A := AmbientRing p)

/-- Primes over the same root-ring prime form one character orbit. -/
theorem ambient_primes_over_root_transitive (P Q : Ideal (AmbientRing p)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under (RootRing p τ) = Q.under (RootRing p τ)) :
    ∃ χ : RootCharacter p τ,
      Q = Ideal.map (ambientCharacterHom p τ χ).toRingHom P := by
  let : Finite (RootCharacter p τ) := canonicalRootCharacters_finite p hp ha τ hτ
  let : Algebra.IsInvariant (RootRing p τ) (AmbientRing p) (RootCharacter p τ) :=
    canonicalRoot_isInvariant p hp ha τ hτ
  obtain ⟨χ, hχ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (RootRing p τ) (AmbientRing p) (RootCharacter p τ) P Q hPQ
  exact ⟨χ, hχ⟩

end Extension
end CanonicalRoots
