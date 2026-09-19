import CanonicalRoots.MonomialFactorInduction
import CanonicalRoots.FermatMonomialReduction

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- A monomial factor/replacement criterion generates all lattice monomials in the actual quotient.
Termination is by positive weighted degree; Fermat replacements preserve that degree. -/
theorem fermat_monomial_generation_of_step {n : ℕ} {ι H : Type*} [AddCommGroup H]
    (p : Fin n → ℕ) (w : Fin n → ℕ) (ψ : (Fin n →₀ ℕ) →+ H)
    (gen : ι → (Fin n →₀ ℕ)) (S : Subalgebra ℂ (AmbientRing p))
    (hgen : ∀ i, ambientQuotient p (monomial (gen i) 1) ∈ S)
    (hpos : ∀ i, 0 < Finsupp.weight w (gen i)) (hψ : ∀ i, ψ (gen i) = 0)
    (hwF : ∀ i j, Finsupp.weight w (Finsupp.single i (p i)) =
      Finsupp.weight w (Finsupp.single j (p j)))
    (hψF : ∀ i j, ψ (Finsupp.single i (p i)) = ψ (Finsupp.single j (p j)))
    (step : ∀ d : Fin n →₀ ℕ, ψ d = 0 →
      d = 0 ∨ (∃ i, gen i ≤ d) ∨
      (∃ i t, d = t + Finsupp.single i (p i) ∧
        ∀ j, j ≠ i → ∃ k, gen k ≤ t + Finsupp.single j (p j))) :
    ∀ d : Fin n →₀ ℕ, ψ d = 0 → ambientQuotient p (monomial d 1) ∈ S := by
  have hind : ∀ k : ℕ, ∀ d : Fin n →₀ ℕ, Finsupp.weight w d = k →
      ψ d = 0 → ambientQuotient p (monomial d 1) ∈ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hwd hψd
      have ih' (b : Fin n →₀ ℕ) (hb : Finsupp.weight w b < k) (hψb : ψ b = 0) :
          ambientQuotient p (monomial b 1) ∈ S := ih _ hb b rfl hψb
      rcases step d hψd with rfl | ⟨i,hi⟩ | ⟨i,t,rfl,ht⟩
      · simp
      · exact monomial_mem_of_factor_induction (ambientQuotient p) S w ψ k ih'
          d (gen i) hi (hpos i) hwd.le hψd (hψ i) (hgen i)
      · apply fermat_monomial_mem_of_other_terms p S t i
        intro j hj
        obtain ⟨l,hl⟩ := ht j hj
        have hwj : Finsupp.weight w (t + Finsupp.single j (p j)) = k := by
          rw [map_add, hwF j i, ← map_add]
          exact hwd
        have hψj : ψ (t + Finsupp.single j (p j)) = 0 := by
          rw [map_add, hψF j i, ← map_add]
          exact hψd
        exact monomial_mem_of_factor_induction (ambientQuotient p) S w ψ k ih'
          _ (gen l) hl (hpos l) hwj.le hψj (hψ l) (hgen l)
  intro d hd
  exact hind (Finsupp.weight w d) d rfl hd

end CanonicalRoots
