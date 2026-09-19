import CanonicalRoots.AdicIdealFunctor

noncomputable section
namespace CanonicalRoots

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]

theorem adicIdealMap_congr (I J : Ideal S) (f g : S →ₐ[R] S)
    (hf : I.map f.toRingHom ≤ J) (hg : I.map g.toRingHom ≤ J) (hfg : f = g) :
    adicIdealMap I J f hf = adicIdealMap I J g hg := by
  subst g
  rfl

/-- Complete an ideal-preserving action using the already proved functoriality. -/
def adicIdealMonoidHom (I : Ideal S) (ρ : G →* (S →ₐ[R] S))
    (hI : ∀ g, I.map (ρ g).toRingHom ≤ I) :
    G →* (AdicCompletion I S →ₐ[R] AdicCompletion I S) where
  toFun g := adicIdealMap I I (ρ g) (hI g)
  map_one' := by
    change adicIdealMap I I (ρ 1) (hI 1) = AlgHom.id R _
    exact (adicIdealMap_congr I I (ρ 1) (AlgHom.id R S) (hI 1) (by simp)
      (map_one ρ)).trans (adicIdealMap_id I _)
  map_mul' g h := by
    change adicIdealMap I I (ρ (g * h)) (hI (g * h)) =
      (adicIdealMap I I (ρ g) (hI g)).comp (adicIdealMap I I (ρ h) (hI h))
    have hgh : I.map ((ρ g).comp (ρ h)).toRingHom ≤ I := by
      change I.map ((ρ g).toRingHom.comp (ρ h).toRingHom) ≤ I
      rw [← Ideal.map_map]
      exact (Ideal.map_mono (hI h)).trans (hI g)
    rw [adicIdealMap_comp I I I (ρ h) (ρ g) (hI h) (hI g) hgh]
    congr 1
    exact map_mul ρ g h

def adicIdealAutomorphism (I : Ideal S) (ρ : G →* (S →ₐ[R] S))
    (hI : ∀ g, I.map (ρ g).toRingHom ≤ I) (g : G) :
    AdicCompletion I S ≃ₐ[R] AdicCompletion I S :=
  AlgEquiv.ofAlgHom (adicIdealMonoidHom I ρ hI g) (adicIdealMonoidHom I ρ hI g⁻¹)
    (by
      change adicIdealMonoidHom I ρ hI g * adicIdealMonoidHom I ρ hI g⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one])
    (by
      change adicIdealMonoidHom I ρ hI g⁻¹ * adicIdealMonoidHom I ρ hI g = 1
      rw [← map_mul, inv_mul_cancel, map_one])

/-- The completed maps are genuine automorphisms satisfying the group law. -/
def adicIdealAction (I : Ideal S) (ρ : G →* (S ≃ₐ[R] S))
    (hI : ∀ g, I.map (ρ g).toRingHom ≤ I) :
    G →* (AdicCompletion I S ≃ₐ[R] AdicCompletion I S) where
  toFun g := adicIdealAutomorphism I ((AlgEquiv.toAlgHomHom R S).comp ρ) hI g
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact (adicIdealMonoidHom I ((AlgEquiv.toAlgHomHom R S).comp ρ) hI).map_one
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact (adicIdealMonoidHom I ((AlgEquiv.toAlgHomHom R S).comp ρ) hI).map_mul g h

end CanonicalRoots
