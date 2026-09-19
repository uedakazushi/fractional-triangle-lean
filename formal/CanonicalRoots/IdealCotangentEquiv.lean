import CanonicalRoots.QuotientCotangent

noncomputable section
namespace CanonicalRoots

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  (J : Ideal A) (K : Ideal B) (e : A ≃ₐ[ℂ] B) (he : J.map e.toRingHom = K)

/-- Cotangent transport for an algebra equivalence carrying the specified ideals to each other. -/
def idealCotangentEquiv : J.Cotangent ≃ₗ[ℂ] K.Cotangent :=
  (quotientCotangentEquiv J e.toAlgHom e.surjective (by
    intro x hx
    have hz : x = 0 := e.injective (hx.trans (map_zero _).symm)
    rw [hz]
    exact Ideal.zero_mem _)).trans ((Ideal.Cotangent.equivOfEq _ _ he).restrictScalars ℂ)

theorem idealCotangentEquiv_mk (x : J) :
    idealCotangentEquiv J K e he (J.toCotangent x) =
      K.toCotangent ⟨e (x : A), he ▸ Ideal.mem_map_of_mem e.toRingHom x.property⟩ := rfl

end CanonicalRoots
