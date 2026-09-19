import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

noncomputable section
namespace CanonicalRoots

variable {R B C G : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [Group G] [Fintype G]

/-- Sum an actual finite automorphism orbit; reindexing proves that the sum is fixed. -/
theorem automorphism_orbit_sum_fixed (ρ : G →* (B ≃ₐ[R] B)) (b : B) (g : G) :
    ρ g (∑ h : G, ρ h b) = ∑ h : G, ρ h b := by
  simp only [map_sum]
  have hm (h : G) : ρ g (ρ h b) = ρ (g * h) b := by
    rw [map_mul]
    rfl
  simp only [hm]
  exact Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun _ => rfl)

/-- Averaging a lift supported at one orbit point produces a globally fixed preimage.
The support and stabilizer conditions are explicit hypotheses to be verified for the actual fiber. -/
theorem exists_fixed_of_supported_lift (ρ : G →* (B ≃ₐ[R] B)) (π : B →ₐ[R] C)
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    [Invertible (((Finset.univ.filter (· ∈ H)).card : ℕ) : R)]
    (b : B) (c : C) (hb : ∀ g : G, π (ρ g b) = if g ∈ H then c else 0) :
    ∃ x : B, (∀ g : G, ρ g x = x) ∧ π x = c := by
  let m : ℕ := (Finset.univ.filter (· ∈ H)).card
  refine ⟨⅟(m : R) • ∑ g : G, ρ g b, ?_, ?_⟩
  · intro g
    rw [map_smul, automorphism_orbit_sum_fixed]
  · rw [map_smul, map_sum]
    simp only [hb]
    have hs : (∑ g : G, if g ∈ H then c else 0) = m • c := by
      rw [← Finset.sum_filter]
      exact Finset.sum_const c
    rw [hs, ← Nat.cast_smul_eq_nsmul R, smul_smul, invOf_mul_self, one_smul]

end CanonicalRoots
