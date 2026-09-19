import CanonicalRoots.AdicIdealFunctor

noncomputable section
namespace CanonicalRoots

/-- An ideal-preserving commutative square remains commutative after completing all four rings. -/
theorem adicIdealMap_square {k R S T U : Type*} [CommRing k] [CommRing R] [CommRing S]
    [CommRing T] [CommRing U] [Algebra k R] [Algebra k S] [Algebra k T] [Algebra k U]
    (I : Ideal R) (J : Ideal S) (K : Ideal T) (L : Ideal U)
    (f : R →ₐ[k] S) (g : R →ₐ[k] T) (a : S →ₐ[k] U) (b : T →ₐ[k] U)
    (hf : I.map f.toRingHom ≤ J) (hg : I.map g.toRingHom ≤ K)
    (ha : J.map a.toRingHom ≤ L) (hb : K.map b.toRingHom ≤ L)
    (h : a.comp f = b.comp g) :
    (adicIdealMap J L a ha).comp (adicIdealMap I J f hf) =
      (adicIdealMap K L b hb).comp (adicIdealMap I K g hg) := by
  have haf : I.map (a.comp f).toRingHom ≤ L := by
    change I.map (a.toRingHom.comp f.toRingHom) ≤ L
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hf).trans ha
  have hbg : I.map (b.comp g).toRingHom ≤ L := by
    change I.map (b.toRingHom.comp g.toRingHom) ≤ L
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hg).trans hb
  rw [adicIdealMap_comp I J L f a hf ha haf, adicIdealMap_comp I K L g b hg hb hbg]
  congr 1

end CanonicalRoots
