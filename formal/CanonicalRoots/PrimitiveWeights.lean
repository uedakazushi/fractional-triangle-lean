import CanonicalRoots.RootEventualNonvanishing
import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem weight_dvd_of_weights_dvd {n : ℕ} (w : Fin n → ℕ) (g : ℕ)
    (hw : ∀ i, g ∣ w i) (d : Fin n →₀ ℕ) : g ∣ Finsupp.weight w d := by
  rw [Finsupp.weight_eq_sum]
  apply Finset.dvd_sum
  intro i _
  simpa [nsmul_eq_mul] using dvd_mul_of_dvd_right (hw i) (d i)

/-- A common weight divisor forces every nonzero homogeneous polynomial degree to be divisible. -/
theorem weightedPiece_eq_bot_of_not_dvd {n : ℕ} (w : Fin n → ℕ) (g m : ℕ)
    (hw : ∀ i, g ∣ w i) (hm : ¬ g ∣ m) :
    weightedHomogeneousSubmodule ℂ w m = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  ext d
  change f.coeff d = 0
  exact hf.coeff_eq_zero d (fun h => hm (h ▸ weight_dvd_of_weights_dvd w g hw d))

theorem presentedPiece_eq_bot_of_not_dvd {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (g m : ℕ) (hw : ∀ i, g ∣ w i) (hm : ¬ g ∣ m) :
    presentedPiece f w m = ⊥ := by
  rw [presentedPiece, weightedPiece_eq_bot_of_not_dvd w g m hw hm, Submodule.map_bot]

namespace GradedAlgEquiv

theorem piece_eq_bot_iff {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] {s : ℕ → Submodule ℂ A} {t : ℕ → Submodule ℂ B}
    (e : GradedAlgEquiv s t) (m : ℕ) : s m = ⊥ ↔ t m = ⊥ := by
  constructor
  · intro hs
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    obtain ⟨x, rfl⟩ := e.toAlgEquiv.surjective y
    have hx := (e.preserves m x).mpr hy
    rw [hs, Submodule.mem_bot] at hx
    simp [hx]
  · intro ht
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hy := (e.preserves m x).mp hx
    rw [ht, Submodule.mem_bot] at hy
    exact e.toAlgEquiv.injective (by simpa using hy)

end GradedAlgEquiv

namespace RootHypersurfacePresentation

/-- Eventual nonvanishing forces primitivity for any actual graded hypersurface presentation. -/
theorem weights_common_divisor_eq_one {n a : ℕ} (hn : 1 ≤ n)
    (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (P : RootHypersurfacePresentation p τ)
    (g : ℕ) (hg : ∀ i, g ∣ P.weights i) : g = 1 := by
  have hgpos : 0 < g := by
    by_contra h
    have heq : g = 0 := by omega
    have hzero : P.weights 0 = 0 := by simpa [heq] using hg 0
    have := P.weights_pos 0
    omega
  obtain ⟨M, hM⟩ := rootPiece_eventually_ne_bot hn p hp ha τ hτ
  have hmm : M ≤ g * M + 1 := by nlinarith
  have hd : g ∣ g * M + 1 := by
    by_contra hd
    have hbot := presentedPiece_eq_bot_of_not_dvd P.polynomial P.weights g _ hg hd
    exact hM _ hmm ((P.graded_equiv.piece_eq_bot_iff _).mp hbot)
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right (dvd_mul_right g M)).mpr hd)

theorem weights_gcd_eq_one {n a : ℕ} (hn : 1 ≤ n)
    (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ) (P : RootHypersurfacePresentation p τ) :
    Finset.univ.gcd P.weights = 1 :=
  P.weights_common_divisor_eq_one hn p hp ha τ hτ _ (fun i => Finset.gcd_dvd (Finset.mem_univ i))

end RootHypersurfacePresentation
end CanonicalRoots
