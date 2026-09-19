import CanonicalRoots.RootPeriodicSignatureRecovery
import CanonicalRoots.WeightedHypersurfaceHilbert

noncomputable section
namespace CanonicalRoots

/-- At a fixed root index, the actual ternary root Hilbert function determines
the signature with multiplicities, without a classification or hypersurface premise. -/
theorem ternary_root_hilbert_signature_eq {a : ℕ} (p q : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (hq : AdmissibleSignature q) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (υ : DegreeGroup q) (hτ : IsCanonicalRoot p a τ) (hυ : IsCanonicalRoot q a υ)
    (he : ∀ m, Module.finrank ℂ (rootPiece p τ m) = Module.finrank ℂ (rootPiece q υ m)) :
    (List.ofFn p : Multiset ℕ) = (List.ofFn q : Multiset ℕ) := by
  let hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  let hq0 : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq.1 i)
  obtain ⟨b, σ, hσ, rfl⟩ := degree_normal_exists p hp0 τ
  obtain ⟨c, ρ, hρ, rfl⟩ := degree_normal_exists q hq0 υ
  let N := (∏ i, p i) * (∏ i, q i)
  have hN : 0 < N := mul_pos (Finset.prod_pos (fun i _ => hp0 i))
    (Finset.prod_pos (fun i _ => hq0 i))
  have hdp : ∀ i, p i ∣ N := fun i =>
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) _
  have hdq : ∀ i, q i ∣ N := fun i =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) _
  exact root_periodic_signature_recovery p q hp.1 hq.1 b c σ ρ (fun i => (hσ i).1)
    (fun i => (hρ i).1) hτ hυ hN hdp hdq
    (ternary_hilbert_periodic_part_eq p q hp hq ha b c σ ρ hτ hυ hN hdp hdq he)

/-- A genuine graded equivalence of ternary canonical-root algebras preserves
the original signature multiset. -/
theorem ternary_root_gradedEquiv_signature_eq {a : ℕ} (p q : Fin 3 → ℕ)
    (hp : AdmissibleSignature p) (hq : AdmissibleSignature q) (ha : 1 ≤ a)
    (τ : DegreeGroup p) (υ : DegreeGroup q) (hτ : IsCanonicalRoot p a τ) (hυ : IsCanonicalRoot q a υ)
    (e : GradedAlgEquiv (rootPiece p τ) (rootPiece q υ)) :
    (List.ofFn p : Multiset ℕ) = (List.ofFn q : Multiset ℕ) :=
  ternary_root_hilbert_signature_eq p q hp hq ha τ υ hτ hυ (fun m => (e.pieceEquiv m).finrank_eq)

end CanonicalRoots
