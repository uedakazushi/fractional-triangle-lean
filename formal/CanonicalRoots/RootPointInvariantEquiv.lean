import CanonicalRoots.RootPointCompletion

noncomputable section
namespace CanonicalRoots

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
  (hp : AdmissibleSignature p) (ha : 1 ≤ a) (hτ : IsCanonicalRoot p a τ)
  (z : AmbientRing p →ₐ[ℂ] ℂ)

include hp ha hτ in
set_option backward.isDefEq.respectTransparency.types false in
/-- Chinese remainder supplies a lift supported at the chosen original point. -/
theorem root_point_supported_lift (c : AdicCompletion (RingHom.ker z.toRingHom) (AmbientRing p)) :
    ∃ b : AmbientRootCompletion p τ (RingHom.ker (rootPoint p τ z).toRingHom),
      rootPointCompletedProjection p τ z b = c ∧
      ∀ χ : RootCharacter p τ, χ ∉ rootPointStabilizer p τ z →
        rootPointCompletedProjection p τ z
          (completedRootCharacterHom p τ (RingHom.ker (rootPoint p τ z).toRingHom) χ b) = 0 := by
  classical
  let : Module.Finite (RootRing p τ) (AmbientRing p) := ambient_finite_over_root p hp ha τ hτ
  let J := RingHom.ker (rootPoint p τ z).toRingHom
  let P := rootFiberPoint p τ z
  let v : ∀ Q : J.primesOver (AmbientRing p), AdicCompletion Q.val (AmbientRing p) := Pi.single P c
  let b := (finiteFiberCompletionEquiv J).symm v
  have hb (Q : J.primesOver (AmbientRing p)) : finiteFiberProjection J Q b = v Q := by
    rw [← finiteFiberCompletionEquiv_apply]
    exact congrFun ((finiteFiberCompletionEquiv J).apply_symm_apply v) Q
  refine ⟨b, ?_, ?_⟩
  · change finiteFiberProjection J P b = c
    rw [hb]
    exact Pi.single_eq_same (M := fun Q : J.primesOver (AmbientRing p) =>
      AdicCompletion Q.val (AmbientRing p)) P c
  · intro χ hχ
    let e := ambientRootAlgEquiv p τ χ
    let Q := (fiberPrimeEquiv J e).symm P
    have he : fiberPrimeEquiv J e Q = P := (fiberPrimeEquiv J e).apply_symm_apply P
    have hQP : Q ≠ P := by
      intro h
      apply hχ
      apply (rootFiberPoint_stabilizer_iff p τ z χ).mp
      exact (congrArg (fiberPrimeEquiv J e) h).symm.trans he
    have hzero : finiteFiberProjection J Q b = 0 := by
      rw [hb]
      dsimp [v]
      exact Pi.single_eq_of_ne hQP _
    have hnat := finiteFiberProjection_equivariant J e Q b
    rw [hzero, map_zero] at hnat
    change finiteFiberProjection J P (adicAlgebraMap J e.toAlgHom b) = 0
    exact (congrArg (fun P' : J.primesOver (AmbientRing p) =>
      finiteFiberProjection J P' (adicAlgebraMap J e.toAlgHom b) = 0) he).mp hnat

include hp ha hτ in
/-- Every element fixed by the point stabilizer lifts to a globally fixed completed element. -/
theorem rootCompletedFixedToPoint_surjective :
    Function.Surjective (rootCompletedFixedToPoint p τ z) := by
  classical
  let : Finite (RootCharacter p τ) := canonicalRootCharacters_finite p hp ha τ hτ
  let : Fintype (RootCharacter p τ) := Fintype.ofFinite _
  let H := rootPointStabilizer p τ z
  let m : ℕ := (Finset.univ.filter (· ∈ H)).card
  have hm : m ≠ 0 := Finset.card_ne_zero.mpr ⟨1, by simp⟩
  let : Invertible (m : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr hm)
  let : Invertible (m : RootRing p τ) := by
    simpa only [map_natCast] using Invertible.map (algebraMap ℂ (RootRing p τ)) (m : ℂ)
  intro c
  obtain ⟨b, hb, hzero⟩ := root_point_supported_lift p τ hp ha hτ z c.val
  have he (χ : RootCharacter p τ) :
      rootPointCompletedProjection p τ z
        (completedRootCharacterAction p τ (RingHom.ker (rootPoint p τ z).toRingHom) χ b) =
        if χ ∈ H then c.val else 0 := by
    split_ifs with hχ
    · change rootPointCompletedProjection p τ z
        (completedRootCharacterHom p τ _ χ b) = c.val
      rw [rootPointCompletedProjection_equivariant p τ z ⟨χ, hχ⟩, hb]
      exact c.property ⟨χ, hχ⟩
    · exact hzero χ hχ
  obtain ⟨x, hx, hxc⟩ := exists_fixed_of_supported_lift
    (completedRootCharacterAction p τ (RingHom.ker (rootPoint p τ z).toRingHom))
    (rootPointCompletedProjection p τ z) H b c.val he
  exact ⟨⟨x, hx⟩, Subtype.ext hxc⟩

include hp ha hτ in
theorem rootCompletedFixedToPoint_injective :
    Function.Injective (rootCompletedFixedToPoint p τ z) := by
  intro x y h
  exact rootCompletedFixed_projection_injective p τ hp ha hτ _ (rootFiberPoint p τ z)
    (congrArg Subtype.val h)

/-- The completed global fixed algebra is the stabilizer fixed algebra of one actual point factor. -/
def rootCompletedFixedPointEquiv :
    completedRootFixed p τ (RingHom.ker (rootPoint p τ z).toRingHom) ≃ₐ[RootRing p τ]
      pointCompletedFixed p τ z :=
  AlgEquiv.ofBijective (rootCompletedFixedToPoint p τ z)
    ⟨rootCompletedFixedToPoint_injective p τ hp ha hτ z,
      rootCompletedFixedToPoint_surjective p τ hp ha hτ z⟩

/-- Actual root completion equals invariants of the actual ambient point completion.
No invariant-ring or classification statement is taken as an assumption. -/
def rootPointCompletedInvariantEquiv :
    AdicCompletion (RingHom.ker (rootPoint p τ z).toRingHom) (RootRing p τ) ≃ₐ[RootRing p τ]
      pointCompletedFixed p τ z :=
  (rootCompletedAlgebraEquiv p τ _ hp ha hτ).trans (rootCompletedFixedPointEquiv p τ hp ha hτ z)

end CanonicalRoots
