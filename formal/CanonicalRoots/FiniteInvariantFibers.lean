import CanonicalRoots.InvariantExtension
import Mathlib.RingTheory.QuasiFinite.Basic

noncomputable section
namespace CanonicalRoots

section GeneralFiber
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (J : Ideal R) [J.IsMaximal]

/-- Above a maximal ideal, containing its extension is precisely lying over it. -/
theorem liesOver_maximal_iff_map_le (Q : Ideal S) [Q.IsPrime] :
    Q.LiesOver J ↔ J.map (algebraMap R S) ≤ Q := by
  constructor
  · intro h
    exact Ideal.map_le_iff_le_comap.mpr (le_of_eq h.over)
  · intro h
    have he : Q.under R = J :=
      (IsCoatom.le_iff_eq (Ideal.isMaximal_def.mp (inferInstance : J.IsMaximal))
        (inferInstance : (Q.under R).IsPrime).ne_top).mp
          (Ideal.map_le_iff_le_comap.mp h)
    exact ⟨he.symm⟩

/-- The radical of a closed fiber is the intersection of the actual primes above its point. -/
theorem radical_map_eq_iInf_primesOver :
    (J.map (algebraMap R S)).radical = ⨅ Q : J.primesOver S, Q.val := by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · apply le_iInf
    intro Q
    exact sInf_le ⟨(liesOver_maximal_iff_map_le J Q.val).mp Q.property.2, Q.property.1⟩
  · apply le_sInf
    intro Q hQ
    let : Q.IsPrime := hQ.2
    exact iInf_le (fun Q : J.primesOver S => Q.val)
      ⟨Q, hQ.2, (liesOver_maximal_iff_map_le J Q).mpr hQ.1⟩

end GeneralFiber

section RootFiber
variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
  (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)

include hp ha hτ

/-- Every fiber of the actual finite root quotient has finitely many prime points. -/
theorem root_primesOver_finite (J : Ideal (RootRing p τ)) :
    (J.primesOver (AmbientRing p)).Finite := by
  let : Module.Finite (RootRing p τ) (AmbientRing p) := ambient_finite_over_root p hp ha τ hτ
  exact Algebra.QuasiFinite.finite_primesOver J

/-- Over a closed root point all the ambient primes are maximal. -/
theorem root_primesOver_maximal (J : Ideal (RootRing p τ)) [J.IsMaximal]
    (Q : J.primesOver (AmbientRing p)) : Q.val.IsMaximal := by
  let : Algebra.IsIntegral (RootRing p τ) (AmbientRing p) := ambient_integral_over_root p hp ha τ hτ
  exact Ideal.primesOver.isMaximal Q

omit hp ha hτ in
/-- The closed-fiber radical has a power contained in the actual extended point ideal. -/
theorem root_fiber_radical_power (J : Ideal (RootRing p τ)) :
    ∃ k : ℕ, (J.map (algebraMap (RootRing p τ) (AmbientRing p))).radical ^ k ≤
      J.map (algebraMap (RootRing p τ) (AmbientRing p)) := by
  exact Ideal.exists_radical_pow_le_of_fg _ (Ideal.fg_of_isNoetherianRing _)

end RootFiber
end CanonicalRoots
