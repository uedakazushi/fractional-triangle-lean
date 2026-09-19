import CanonicalRoots.AdicCompleteLift

noncomputable section
namespace CanonicalRoots

/-- The continuity bound for uniqueness need only be checked on elements of the original ideal. -/
theorem adicCompletion_algHom_ext_of_base {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (I : Ideal R) (hI : I.FG) (J : Ideal S) [IsHausdorff J S]
    (f g : AdicCompletion I R →ₐ[k] S)
    (hf : ∀ r ∈ I, f (algebraMap R (AdicCompletion I R) r) ∈ J)
    (hfg : ∀ r : R, f (algebraMap R (AdicCompletion I R) r) =
      g (algebraMap R (AdicCompletion I R) r)) : f = g := by
  apply adicCompletion_algHom_ext I hI J f g
  · rw [Ideal.map_map]
    exact Ideal.map_le_iff_le_comap.mpr hf
  · rw [Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change g (algebraMap R (AdicCompletion I R) r) ∈ J
    rw [← hfg r]
    exact hf r hr
  · exact hfg

end CanonicalRoots
