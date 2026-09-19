import CanonicalRoots.AmbientBasis
import CanonicalRoots.CyclicQuotientSingularity

noncomputable section
namespace CanonicalRoots
open MvPolynomial

abbrev CyclicModelRing (s : ℕ) := PresentedRing (cyclicQuotientEquation (1 : Fin 3) 2 0 s)

def cyclicSplitPolynomial (s : ℕ) : Polynomial (MvPolynomial (Fin 2) ℂ) :=
  Polynomial.X ^ s - Polynomial.C (X 0 * X 1)

theorem cyclicSplitPolynomial_monic (s : ℕ) (hs : 0 < s) : (cyclicSplitPolynomial s).Monic :=
  Polynomial.monic_X_pow_sub_C _ (ne_of_gt hs)

@[simp] theorem cyclicSplitPolynomial_natDegree (s : ℕ) :
    (cyclicSplitPolynomial s).natDegree = s := Polynomial.natDegree_X_pow_sub_C

def cyclicAdjoinEquiv (s : ℕ) : CyclicModelRing s ≃ₐ[ℂ] AdjoinRoot (cyclicSplitPolynomial s) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.finSuccEquiv ℂ 2) (by
    have he : MvPolynomial.finSuccEquiv ℂ 2 (cyclicQuotientEquation (1 : Fin 3) 2 0 s) =
        -cyclicSplitPolynomial s := by
      simp only [cyclicQuotientEquation, map_sub, map_mul, map_pow, finSuccEquiv_X_zero,
        show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
        show (2 : Fin 3) = (1 : Fin 2).succ from rfl, finSuccEquiv_X_succ]
      simp [cyclicSplitPolynomial, Polynomial.C_mul]
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {cyclicSplitPolynomial s} =
      Ideal.span {MvPolynomial.finSuccEquiv ℂ 2 (cyclicQuotientEquation (1 : Fin 3) 2 0 s)}
    rw [he, Ideal.span_singleton_neg])

def cyclicPowerBasis (s : ℕ) (hs : 0 < s) :
    Module.Basis (Fin s) (MvPolynomial (Fin 2) ℂ) (AdjoinRoot (cyclicSplitPolynomial s)) :=
  (AdjoinRoot.powerBasis' (cyclicSplitPolynomial_monic s hs)).basis.reindex
    (finCongr (cyclicSplitPolynomial_natDegree s))

@[simp] theorem cyclicPowerBasis_apply (s : ℕ) (hs : 0 < s) (k : Fin s) :
    cyclicPowerBasis s hs k = AdjoinRoot.root (cyclicSplitPolynomial s) ^ (k : ℕ) := by
  simp [cyclicPowerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

def cyclicMonomialBasis (s : ℕ) (hs : 0 < s) :
    Module.Basis ((Fin 2 →₀ ℕ) × Fin s) ℂ (CyclicModelRing s) :=
  ((MvPolynomial.basisMonomials (Fin 2) ℂ).smulTower (cyclicPowerBasis s hs)).map
    (cyclicAdjoinEquiv s).symm.toLinearEquiv

@[simp] theorem cyclicMonomialBasis_apply (s : ℕ) (hs : 0 < s) (d : Fin 2 →₀ ℕ) (k : Fin s) :
    cyclicMonomialBasis s hs (d, k) =
      Ideal.Quotient.mkₐ ℂ _ (monomial (d.cons (k : ℕ)) 1) := by
  apply (cyclicAdjoinEquiv s).injective
  simp only [cyclicMonomialBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, Module.Basis.smulTower_apply, coe_basisMonomials,
    cyclicPowerBasis_apply]
  change _ = AdjoinRoot.mk (cyclicSplitPolynomial s)
    (MvPolynomial.finSuccEquiv ℂ 2 (monomial (d.cons (k : ℕ)) 1))
  rw [finSuccEquiv_monomial_cons, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.of,
    RingHom.comp_apply, map_mul, map_pow, AdjoinRoot.mk_X]

def cyclicPolynomialMap (s : ℕ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  aeval ![X 0 * X 1, X 0 ^ s, X 1 ^ s]

theorem cyclicPolynomialMap_relation (s : ℕ) :
    cyclicPolynomialMap s (cyclicQuotientEquation (1 : Fin 3) 2 0 s) = 0 := by
  simp [cyclicPolynomialMap, cyclicQuotientEquation, mul_pow]

/-- The actual map C[U,V,W]/(UV-W^s) → C[x,y], with U=x^s,V=y^s,W=xy. -/
def cyclicQuotientMap (s : ℕ) : CyclicModelRing s →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  Ideal.Quotient.liftₐ _ (cyclicPolynomialMap s) (by
    change Ideal.span {cyclicQuotientEquation (1 : Fin 3) 2 0 s} ≤
      RingHom.ker (cyclicPolynomialMap s).toRingHom
    rw [Ideal.span_singleton_le_iff_mem]
    exact cyclicPolynomialMap_relation s)

@[simp] theorem cyclicQuotientMap_mk (s : ℕ) (f : MvPolynomial (Fin 3) ℂ) :
    cyclicQuotientMap s (Ideal.Quotient.mkₐ ℂ _ f) = cyclicPolynomialMap s f := rfl

def cyclicImageExponent (s : ℕ) (q : (Fin 2 →₀ ℕ) × Fin s) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![s * q.1 0 + q.2, s * q.1 1 + q.2]

theorem cyclicImageExponent_injective (s : ℕ) (hs : 0 < s) :
    Function.Injective (cyclicImageExponent s) := by
  intro q r he
  have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
  have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
  change s * q.1 0 + (q.2 : ℕ) = s * r.1 0 + (r.2 : ℕ) at h0
  change s * q.1 1 + (q.2 : ℕ) = s * r.1 1 + (r.2 : ℕ) at h1
  have hk : (q.2 : ℕ) = r.2 := by
    have hm := congrArg (fun m : ℕ => m % s) h0
    simpa [Nat.add_mod, Nat.mod_eq_of_lt q.2.isLt, Nat.mod_eq_of_lt r.2.isLt] using hm
  have hd : q.1 = r.1 := by
    rw [hk] at h0 h1
    apply Finsupp.ext
    intro i
    fin_cases i
    · exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_right_cancel h0)
    · exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_right_cancel h1)
  exact Prod.ext hd (Fin.ext hk)

theorem cyclicQuotientMap_basis (s : ℕ) (hs : 0 < s) (q : (Fin 2 →₀ ℕ) × Fin s) :
    cyclicQuotientMap s (cyclicMonomialBasis s hs q) = monomial (cyclicImageExponent s q) 1 := by
  obtain ⟨d, k⟩ := q
  rw [cyclicMonomialBasis_apply, cyclicQuotientMap_mk]
  simp only [cyclicPolynomialMap, aeval_monomial, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (by simp), monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ, cyclicImageExponent,
    pow_add, pow_mul, mul_pow]
  ring

/-- Normal-form monomials have distinct images, proving injectivity of the actual quotient map. -/
theorem cyclicQuotientMap_injective (s : ℕ) (hs : 0 < s) : Function.Injective (cyclicQuotientMap s) := by
  let b := cyclicMonomialBasis s hs
  have hi : LinearIndependent ℂ (fun q => cyclicQuotientMap s (b q)) := by
    simp only [b, cyclicQuotientMap_basis]
    exact (MvPolynomial.basisMonomials (Fin 2) ℂ).linearIndependent.comp
      (cyclicImageExponent s) (cyclicImageExponent_injective s hs)
  have he : b.constr ℂ (fun q => cyclicQuotientMap s (b q)) = (cyclicQuotientMap s).toLinearMap := by
    apply b.ext
    intro q
    simp
  change Function.Injective (cyclicQuotientMap s).toLinearMap
  rw [← he]
  exact b.injective_constr_of_linearIndependent hi

/-- The image exponent pairs are exactly those with equal residues modulo s. -/
theorem cyclicImageExponent_range_iff (s : ℕ) (hs : 0 < s) (d : Fin 2 →₀ ℕ) :
    d ∈ Set.range (cyclicImageExponent s) ↔ d 0 % s = d 1 % s := by
  constructor
  · rintro ⟨q, rfl⟩
    simp [cyclicImageExponent, Nat.add_mod]
  · intro hd
    let e : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![d 0 / s, d 1 / s]
    refine ⟨(e, ⟨d 0 % s, Nat.mod_lt _ hs⟩), ?_⟩
    apply Finsupp.ext
    intro i
    fin_cases i
    · change s * (d 0 / s) + d 0 % s = d 0
      exact Nat.div_add_mod _ _
    · change s * (d 1 / s) + d 0 % s = d 1
      rw [hd]
      exact Nat.div_add_mod _ _

theorem coeff_cyclicQuotientMap_eq_zero (s : ℕ) (hs : 0 < s)
    (f : CyclicModelRing s) (d : Fin 2 →₀ ℕ) (hd : d 0 % s ≠ d 1 % s) :
    (cyclicQuotientMap s f).coeff d = 0 := by
  classical
  have he := (cyclicMonomialBasis s hs).linearCombination_repr f
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at he
  rw [← he, map_sum, coeff_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [map_smul, cyclicQuotientMap_basis, coeff_smul, coeff_monomial]
  have hne : cyclicImageExponent s q ≠ d := by
    intro hq
    apply hd
    exact (cyclicImageExponent_range_iff s hs d).mp ⟨q, hq⟩
  simp [hne]

/-- The actual quotient map has precisely the expected monomial support. -/
theorem mem_cyclicQuotientMap_range_iff (s : ℕ) (hs : 0 < s) (f : MvPolynomial (Fin 2) ℂ) :
    f ∈ (cyclicQuotientMap s).range ↔ ∀ d, f.coeff d ≠ 0 → d 0 % s = d 1 % s := by
  classical
  constructor
  · rintro ⟨g, rfl⟩ d hd
    by_contra hn
    exact hd (coeff_cyclicQuotientMap_eq_zero s hs g d hn)
  · intro hf
    rw [f.as_sum]
    apply Subalgebra.sum_mem
    intro d hd
    obtain ⟨q, hq⟩ := (cyclicImageExponent_range_iff s hs d).mpr (hf d (mem_support_iff.mp hd))
    have hm : monomial d (1 : ℂ) ∈ (cyclicQuotientMap s).range :=
      ⟨cyclicMonomialBasis s hs q, (cyclicQuotientMap_basis s hs q).trans
        (congrArg (fun e : Fin 2 →₀ ℕ => monomial e (1 : ℂ)) hq)⟩
    simpa only [smul_monomial, smul_eq_mul, mul_one] using
      (cyclicQuotientMap s).range.smul_mem hm (f.coeff d)

end CanonicalRoots
