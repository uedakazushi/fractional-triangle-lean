import CanonicalRoots.CoxCandidateMap

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- A factor of positive weight reduces a monomial-generation problem to the induction hypothesis.
The residue homomorphism records the lattice condition and is retained after division. -/
theorem monomial_mem_of_factor_induction {σ H A : Type*} [AddCommGroup H]
    [CommRing A] [Algebra ℂ A] (q : MvPolynomial σ ℂ →ₐ[ℂ] A) (S : Subalgebra ℂ A)
    (w : σ → ℕ) (ψ : (σ →₀ ℕ) →+ H) (bound : ℕ)
    (ih : ∀ b : σ →₀ ℕ, Finsupp.weight w b < bound → ψ b = 0 → q (monomial b 1) ∈ S)
    (d e : σ →₀ ℕ) (he : e ≤ d) (hweight : 0 < Finsupp.weight w e)
    (hd : Finsupp.weight w d ≤ bound) (hψd : ψ d = 0) (hψe : ψ e = 0)
    (hgen : q (monomial e 1) ∈ S) : q (monomial d 1) ∈ S := by
  classical
  let b := d - e
  have hdb : e + b = d := add_tsub_cancel_of_le he
  have hwb : Finsupp.weight w b < bound := by
    have hh := congrArg (Finsupp.weight w) hdb
    rw [map_add] at hh
    omega
  have hψb : ψ b = 0 := by
    have hh := congrArg ψ hdb
    simpa only [map_add, hψe, zero_add, hψd] using hh
  have hb := ih b hwb hψb
  have hm : monomial d (1 : ℂ) = monomial e 1 * monomial b 1 := by
    rw [monomial_mul_monomial, one_mul, hdb]
  rw [hm, map_mul]
  exact S.mul_mem hgen hb

end CanonicalRoots
