import CanonicalRoots.CoxMonicInjection
import CanonicalRoots.RootCoordinateCongruence
import CanonicalRoots.PermutedRootMonomials

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem candidateSignature_monic_last {e : TernaryCandidate}
    (hk : e.kind = .II ∨ e.kind = .III) : candidateSignature e 2 = e.gamma := by
  rcases e with ⟨kind,α,β,γ⟩
  rcases hk with rfl | rfl <;> simp [candidateSignature,Cox.signature]

theorem candidateSignature_monic_middle_dvd {a : ℕ} {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III) :
    e.gamma ∣ candidateSignature e 1 := by
  have hh : (e.gamma : ℤ) ∣ (candidateSignature e 1 : ℤ) := by
    rw [candidateSignature_cast he]
    rcases e with ⟨kind,α,β,γ⟩
    rcases hk with rfl | rfl <;> simp [Cox.signature]
  exact_mod_cast hh

/-- Every bounded monomial of root degree factors through the Cox monomials in types II and III. -/
theorem candidate_monic_root_preimage {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ)
    (d : Fin 3 →₀ ℕ) (hd2 : d 2 < e.gamma)
    (hd : ∃ m : ℕ, Finsupp.weight (xDegree (candidateSignature e)) d = m • τ) :
    ∃ b : Fin 3 →₀ ℕ, candidateExponentMap e b = d := by
  have hp : ∀ i, 0 < candidateSignature e i := fun i => by
    have := candidateSignature_ge_two he i
    omega
  have hγ2 : e.gamma ∣ candidateSignature e 2 := by rw [candidateSignature_monic_last hk]
  have h12 := root_monomial_coordinate_congruence (candidateSignature e) hp τ hτ 1 2
    (candidateSignature_monic_middle_dvd he hk) hγ2 d hd
  have hd1 := congruence_bounded_decomposition hd2 h12
  rcases e with ⟨kind,α,β,γ⟩
  rcases hk with rfl | rfl
  · refine ⟨Finsupp.equivFunOnFinite.symm ![d 0, d 1 / γ, d 2], ?_⟩
    ext i
    fin_cases i <;> simp [candidateExponentMap, Fin.sum_univ_three,
      candidateMonomialExponent, Cox.monomials] <;> simpa [Nat.mul_comm] using hd1.symm
  · have hγ0 : γ ∣ candidateSignature ⟨.III,α,β,γ⟩ 0 := by
      have hh : (γ : ℤ) ∣ (candidateSignature ⟨.III,α,β,γ⟩ 0 : ℤ) := by
        rw [candidateSignature_cast he]
        simp [Cox.signature]
      exact_mod_cast hh
    have h02 := root_monomial_coordinate_congruence (candidateSignature ⟨.III,α,β,γ⟩) hp τ hτ 0 2
      hγ0 hγ2 d hd
    have hd0 := congruence_bounded_decomposition hd2 h02
    refine ⟨Finsupp.equivFunOnFinite.symm ![d 0 / γ, d 1 / γ, d 2], ?_⟩
    ext i
    fin_cases i <;> simp [candidateExponentMap, Fin.sum_univ_three,
      candidateMonomialExponent, Cox.monomials] <;>
      first | simpa [Nat.mul_comm] using hd0.symm | simpa [Nat.mul_comm] using hd1.symm

theorem candidateQuotientMap_surjective_of_monic {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    Function.Surjective (candidateQuotientMap ha he τ hτ) := by
  let sw := Equiv.swap (0 : Fin 3) 2
  have hlast : candidateSignature e (sw 0) = e.gamma := by
    simpa [sw] using candidateSignature_monic_last hk
  apply rootMap_surjective_of_permuted_monomials (candidateSignature e) sw
    (by have := candidateSignature_ge_two he (sw 0); omega) τ
  intro d hdBound hdRoot
  have hd2 : d 2 < e.gamma := by
    simpa only [sw,Equiv.swap_apply_left,candidateSignature_monic_last hk] using hdBound
  obtain ⟨b,hb⟩ := candidate_monic_root_preimage ha he hk τ hτ d hd2 hdRoot
  refine ⟨(Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) (monomial b 1), ?_⟩
  rw [candidateQuotientMap_monomial_val, hb]

/-- A concrete algebra equivalence of the actual Cox quotient and actual root ring. -/
def candidateMonicAlgEquiv {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    PresentedRing (candidateRelation e) ≃ₐ[ℂ] RootRing (candidateSignature e) τ :=
  AlgEquiv.ofBijective (candidateQuotientMap ha he τ hτ)
    ⟨candidateQuotientMap_injective_of_monic ha he hk τ hτ,
      candidateQuotientMap_surjective_of_monic ha he hk τ hτ⟩

end CanonicalRoots
