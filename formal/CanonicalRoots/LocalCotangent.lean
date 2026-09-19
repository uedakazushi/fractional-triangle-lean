import CanonicalRoots.MinimalGenerators

noncomputable section
namespace CanonicalRoots
open IsLocalRing

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (J : Ideal A) [J.IsMaximal]
variable (S : Type*) [CommRing S] [Algebra A S] [Algebra ℂ S] [IsScalarTower ℂ A S]
  [IsLocalization.AtPrime S J] [IsLocalRing S]

def localCotangentMap : J.Cotangent →ₗ[ℂ] (maximalIdeal S).Cotangent :=
  Ideal.mapCotangent J (maximalIdeal S) (IsScalarTower.toAlgHom ℂ A S) (by
    intro x hx
    change algebraMap A S x ∈ maximalIdeal S
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal J S]
    exact Ideal.mem_map_of_mem _ hx)

theorem localCotangentMap_injective : Function.Injective (localCotangentMap J S) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  obtain ⟨x, rfl⟩ := J.toCotangent_surjective z
  change J.toCotangent x = 0
  apply (J.toCotangent_eq_zero x).mpr
  have hqx : algebraMap A S x ∈ maximalIdeal S ^ 2 :=
    ((maximalIdeal S).toCotangent_eq_zero _).mp hz
  change (x : A) ∈ (maximalIdeal S ^ 2).under A at hqx
  rwa [IsLocalization.AtPrime.under_maximalIdeal_pow J S] at hqx

theorem localCotangentMap_surjective : Function.Surjective (localCotangentMap J S) := by
  intro z
  obtain ⟨y, rfl⟩ := (maximalIdeal S).toCotangent_surjective z
  obtain ⟨u, hu⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdealPow J S 2).surjective
    (Ideal.Quotient.mk (maximalIdeal S ^ 2) (y : S))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
  have heq : Ideal.Quotient.mk (maximalIdeal S ^ 2) (algebraMap A S x) =
      Ideal.Quotient.mk (maximalIdeal S ^ 2) (y : S) := hu
  have hsub : algebraMap A S x - y ∈ maximalIdeal S ^ 2 :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp heq
  have hxS : algebraMap A S x ∈ maximalIdeal S := by
    simpa using (maximalIdeal S).add_mem (Ideal.pow_le_self two_ne_zero hsub) y.property
  have hx : x ∈ J := by
    change x ∈ (maximalIdeal S).under A at hxS
    rwa [IsLocalization.AtPrime.under_maximalIdeal S J] at hxS
  refine ⟨J.toCotangent ⟨x, hx⟩, ?_⟩
  apply (maximalIdeal S).cotangentToQuotientSquare_injective
  exact heq

/-- Localization at a maximal ideal preserves its actual cotangent space. -/
def localCotangentEquiv : J.Cotangent ≃ₗ[ℂ] (maximalIdeal S).Cotangent :=
  LinearEquiv.ofBijective (localCotangentMap J S)
    ⟨localCotangentMap_injective J S, localCotangentMap_surjective J S⟩

/-- Localization also preserves the residue algebra, not just its abstract ring. -/
def localResidueEquiv : (A ⧸ J) ≃ₐ[ℂ] ResidueField S :=
  (Ideal.quotientEquivAlgOfEq ℂ (pow_one J).symm).trans
    (((IsLocalization.AtPrime.equivQuotMaximalIdealPow J S 1).restrictScalars ℂ).trans
      (Ideal.quotientEquivAlgOfEq ℂ (pow_one (maximalIdeal S))))

end CanonicalRoots
