import CanonicalRoots.OriginCotangent

noncomputable section
namespace CanonicalRoots

section General
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- The cotangent map induced by a surjective algebra homomorphism. -/
def quotientCotangentMap (J : Ideal A) (q : A →ₐ[ℂ] B) :
    J.Cotangent →ₗ[ℂ] (J.map q.toRingHom).Cotangent :=
  Ideal.mapCotangent J (J.map q.toRingHom) q
    (fun _ hx => Ideal.mem_map_of_mem q.toRingHom hx)

theorem quotientCotangentMap_surjective (J : Ideal A) (q : A →ₐ[ℂ] B)
    (hq : Function.Surjective q) : Function.Surjective (quotientCotangentMap J q) := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := (J.map q.toRingHom).toCotangent_surjective z
  obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective q.toRingHom hq).mp hy
  exact ⟨J.toCotangent ⟨x, hx⟩, rfl⟩

/-- Relations lying in the square of the ideal impose no new cotangent relations. -/
theorem quotientCotangentMap_injective (J : Ideal A) (q : A →ₐ[ℂ] B)
    (hq : Function.Surjective q) (hker : RingHom.ker q.toRingHom ≤ J ^ 2) :
    Function.Injective (quotientCotangentMap J q) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  obtain ⟨x, rfl⟩ := J.toCotangent_surjective z
  change J.toCotangent x = 0
  apply (J.toCotangent_eq_zero x).mpr
  have hqx : q x ∈ (J.map q.toRingHom) ^ 2 :=
    ((J.map q.toRingHom).toCotangent_eq_zero _).mp hz
  rw [← Ideal.map_pow] at hqx
  obtain ⟨y, hy, heq⟩ := (Ideal.mem_map_iff_of_surjective q.toRingHom hq).mp hqx
  change q y = q x at heq
  have hsub : (x : A) - y ∈ RingHom.ker q.toRingHom := by
    change q ((x : A) - y) = 0
    simp [map_sub, heq]
  simpa using (J ^ 2).add_mem (hker hsub) hy

def quotientCotangentEquiv (J : Ideal A) (q : A →ₐ[ℂ] B)
    (hq : Function.Surjective q) (hker : RingHom.ker q.toRingHom ≤ J ^ 2) :
    J.Cotangent ≃ₗ[ℂ] (J.map q.toRingHom).Cotangent :=
  LinearEquiv.ofBijective (quotientCotangentMap J q)
    ⟨quotientCotangentMap_injective J q hq hker, quotientCotangentMap_surjective J q hq⟩
end General

end CanonicalRoots
