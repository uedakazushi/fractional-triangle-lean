import CanonicalRoots.CoxExplicitPolynomials
import CanonicalRoots.CoxCandidateMap

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def candidateExponentMap (e : TernaryCandidate) (d : Fin 3 →₀ ℕ) : Fin 3 →₀ ℕ :=
  ∑ i, d i • candidateMonomialExponent e i

theorem candidateExponentMap_last {e : TernaryCandidate}
    (hk : e.kind = .II ∨ e.kind = .III) (d : Fin 3 →₀ ℕ) :
    candidateExponentMap e d 2 = d 2 := by
  rcases e with ⟨kind,α,β,γ⟩
  rcases hk with rfl | rfl <;>
    simp [candidateExponentMap, Fin.sum_univ_three, candidateMonomialExponent, Cox.monomials]

theorem candidateExponentMap_injective {e : TernaryCandidate}
    (hk : e.kind = .II ∨ e.kind = .III) (hγ : 0 < e.gamma) :
    Function.Injective (candidateExponentMap e) := by
  rcases e with ⟨kind,α,β,γ⟩
  intro d b h
  have h0 := congrArg (fun x => x (0 : Fin 3)) h
  have h1 := congrArg (fun x => x (1 : Fin 3)) h
  have h2 := congrArg (fun x => x (2 : Fin 3)) h
  rcases hk with rfl | rfl <;>
    simp [candidateExponentMap, Fin.sum_univ_three, candidateMonomialExponent, Cox.monomials] at h0 h1 h2 <;>
    ext i <;> fin_cases i <;> simp at hγ <;>
    first | change d 0 = b 0 | change d 1 = b 1 | change d 2 = b 2
  all_goals nlinarith

theorem candidateQuotientMap_monomial_val {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (τ : DegreeGroup (candidateSignature e))
    (hτ : IsCanonicalRoot (candidateSignature e) a τ) (d : Fin 3 →₀ ℕ) :
    (candidateQuotientMap ha he τ hτ
      ((Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) (monomial d 1)) :
        AmbientRing (candidateSignature e)) =
      ambientQuotient (candidateSignature e) (monomial (candidateExponentMap e d) 1) := by
  rw [candidateQuotientMap_mk]
  change ((rootSubalgebra (candidateSignature e) τ).val.comp (candidatePolynomialMap ha he τ hτ))
    (monomial d 1) = _
  rw [candidatePolynomialMap_val]
  change ambientQuotient (candidateSignature e) (aeval (candidateMonomial e) (monomial d (1 : ℂ))) = _
  rw [show aeval (candidateMonomial e) (monomial d (1 : ℂ)) =
      monomial (candidateExponentMap e d) 1 from
    aeval_monomial_one_matrix d (candidateMonomialExponent e)]

theorem separatedPermutedMonomials_span {n : ℕ} (k : ℕ) (hk : 0 < k)
    (g : MvPolynomial (Fin n) ℂ) (e : Equiv.Perm (Fin (n + 1))) :
    Submodule.span ℂ (Set.range (fun d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < k} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename e (separatedRelation k g)})) (monomial d.val 1))) = ⊤ := by
  have hh : (fun d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < k} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename e (separatedRelation k g)})) (monomial d.val 1)) =
      separatedPermutedBoundedBasis k hk g e := by
    funext d
    exact (separatedPermutedBoundedBasis_apply k hk g e d).symm
  rw [hh]
  exact Module.Basis.span_eq _

theorem candidateMonicMonomials_span {e : TernaryCandidate}
    (hk : e.kind = .II ∨ e.kind = .III) (hγ : 0 < e.gamma) :
    Submodule.span ℂ (Set.range (fun d : {d : Fin 3 →₀ ℕ // d 2 < e.gamma} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) (monomial d.val 1))) = ⊤ := by
  rcases e with ⟨kind,α,β,γ⟩
  rcases hk with rfl | rfl
  · rw [oneArrow_relation_separated]
    convert separatedPermutedMonomials_span γ hγ
      (X (1 : Fin 2) ^ α * X 0 + X 0 ^ β) (Equiv.swap (0 : Fin 3) 2) using 1 <;>
      norm_num [Equiv.swap_apply_def]
    congr 1
  · rw [twoCycle_relation_separated]
    convert separatedPermutedMonomials_span γ hγ
      (X (1 : Fin 2) ^ α * X 0 + X 1 * X 0 ^ β) (Equiv.swap (0 : Fin 3) 2) using 1 <;>
      norm_num [Equiv.swap_apply_def]
    congr 1

/-- Types II and III embed into the actual Fermat quotient, by independent monomial images. -/
theorem candidateQuotientMap_injective_of_monic {a : ℕ} (ha : 1 ≤ a) {e : TernaryCandidate}
    (he : ArithmeticTernary a e) (hk : e.kind = .II ∨ e.kind = .III)
    (τ : DegreeGroup (candidateSignature e)) (hτ : IsCanonicalRoot (candidateSignature e) a τ) :
    Function.Injective (candidateQuotientMap ha he τ hτ) := by
  let sw := Equiv.swap (0 : Fin 3) 2
  let p := candidateSignature e
  have hγ : 0 < e.gamma := by have := he.2.2.1; omega
  have hp2 : p (sw 0) = e.gamma := by
    rcases e with ⟨kind,α,β,γ⟩
    rcases hk with rfl | rfl <;> simp [p,sw,candidateSignature,Cox.signature]
  let b := ambientPermutedBoundedBasis p sw (by rw [hp2]; exact hγ)
  let u : {d : Fin 3 →₀ ℕ // d 2 < e.gamma} →
      {d : Fin 3 →₀ ℕ // d (sw 0) < p (sw 0)} := fun d =>
    ⟨candidateExponentMap e d.val, by
      rw [hp2]
      simpa only [sw, Equiv.swap_apply_left, candidateExponentMap_last hk] using d.property⟩
  have hu : Function.Injective u := by
    intro d c h
    apply Subtype.ext
    exact candidateExponentMap_injective hk hγ (congrArg Subtype.val h)
  let f := (rootSubalgebra p τ).val.toLinearMap.comp (candidateQuotientMap ha he τ hτ).toLinearMap
  let v := fun d : {d : Fin 3 →₀ ℕ // d 2 < e.gamma} =>
    (Ideal.Quotient.mkₐ ℂ (Ideal.span {candidateRelation e})) (monomial d.val 1)
  have hv : Submodule.span ℂ (Set.range v) = ⊤ := candidateMonicMonomials_span hk hγ
  have hfv : f ∘ v = fun d => b (u d) := by
    funext d
    rw [ambientPermutedBoundedBasis_apply]
    exact candidateQuotientMap_monomial_val ha he τ hτ d.val
  have hinj : Function.Injective f := LinearMap.injective_of_linearIndependent hv (by
    rw [hfv]
    exact b.linearIndependent.comp u hu)
  intro x y h
  exact hinj (congrArg (fun r : RootRing p τ => (r : AmbientRing p)) h)

end CanonicalRoots
