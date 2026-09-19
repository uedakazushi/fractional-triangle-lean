import CanonicalRoots.Semantics

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Isolate X_0 to give a monic equation over the other polynomial variables. -/
def splitFermat {n : ℕ} (p : Fin (n + 1) → ℕ) : Polynomial (MvPolynomial (Fin n) ℂ) :=
  Polynomial.X ^ p 0 + Polynomial.C (fermat (fun i => p i.succ))

theorem finSuccEquiv_fermat {n : ℕ} (p : Fin (n + 1) → ℕ) :
    MvPolynomial.finSuccEquiv ℂ n (fermat p) = splitFermat p := by
  simp [fermat, Fin.sum_univ_succ, splitFermat, map_sum, finSuccEquiv_X_zero, finSuccEquiv_X_succ]

theorem splitFermat_monic {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0) :
    (splitFermat p).Monic := Polynomial.monic_X_pow_add_C _ (ne_of_gt hp)

@[simp] theorem splitFermat_natDegree {n : ℕ} (p : Fin (n + 1) → ℕ) :
    (splitFermat p).natDegree = p 0 := Polynomial.natDegree_X_pow_add_C

/-- This is an equivalence of the actual quotients, obtained by changing polynomial coordinates. -/
def ambientAdjoinEquiv {n : ℕ} (p : Fin (n + 1) → ℕ) :
    AmbientRing p ≃ₐ[ℂ] AdjoinRoot (splitFermat p) :=
  Ideal.quotientEquivAlg (fermatIdeal p) (Ideal.span {splitFermat p})
    (MvPolynomial.finSuccEquiv ℂ n) (by
      simp [fermatIdeal, Ideal.map_span, Set.image_singleton, finSuccEquiv_fermat])

@[simp] theorem ambientAdjoinEquiv_quotient {n : ℕ} (p : Fin (n + 1) → ℕ)
    (f : MvPolynomial (Fin (n + 1)) ℂ) :
    ambientAdjoinEquiv p (ambientQuotient p f) =
      AdjoinRoot.mk (splitFermat p) (MvPolynomial.finSuccEquiv ℂ n f) := rfl

/-- Free basis over the polynomial ring on X_1,...,X_n. -/
def splitPowerBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0) :
    Module.Basis (Fin (p 0)) (MvPolynomial (Fin n) ℂ) (AdjoinRoot (splitFermat p)) :=
  (AdjoinRoot.powerBasis' (splitFermat_monic p hp)).basis.reindex (finCongr (splitFermat_natDegree p))

@[simp] theorem splitPowerBasis_apply {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (i : Fin (p 0)) : splitPowerBasis p hp i = AdjoinRoot.root (splitFermat p) ^ (i : ℕ) := by
  simp [splitPowerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- A full complex vector-space basis of the actual Fermat quotient. -/
def ambientMonomialBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0) :
    Module.Basis ((Fin n →₀ ℕ) × Fin (p 0)) ℂ (AmbientRing p) :=
  ((MvPolynomial.basisMonomials (Fin n) ℂ).smulTower (splitPowerBasis p hp)).map
    (ambientAdjoinEquiv p).symm.toLinearEquiv

theorem finSuccEquiv_monomial_cons {n : ℕ} (d : Fin n →₀ ℕ) (k : ℕ) (c : ℂ) :
    MvPolynomial.finSuccEquiv ℂ n (monomial (d.cons k) c) =
      Polynomial.monomial k (monomial d c) := by
  classical
  ext j t
  rw [finSuccEquiv_coeff_coeff, coeff_monomial, Polynomial.coeff_monomial]
  simp only [Finsupp.cons_injective2.eq_iff]
  by_cases hkj : k = j <;> by_cases hdt : d = t <;> simp [hkj, hdt, coeff_monomial]

theorem ambientMonomialBasis_apply {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (d : Fin n →₀ ℕ) (k : Fin (p 0)) :
    ambientMonomialBasis p hp (d, k) = ambientQuotient p (monomial (d.cons k) 1) := by
  apply (ambientAdjoinEquiv p).injective
  simp only [ambientMonomialBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, Module.Basis.smulTower_apply, coe_basisMonomials,
    splitPowerBasis_apply, ambientAdjoinEquiv_quotient, finSuccEquiv_monomial_cons]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.of,
    RingHom.comp_apply, map_mul, map_pow, AdjoinRoot.mk_X]

theorem ambientMonomialBasis_homogeneous {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (q : (Fin n →₀ ℕ) × Fin (p 0)) :
    ambientMonomialBasis p hp q ∈ ambientPiece p (Finsupp.weight (xDegree p) (q.1.cons (q.2 : ℕ))) := by
  rw [ambientMonomialBasis_apply]
  exact Submodule.mem_map.mpr ⟨_, isWeightedHomogeneous_monomial _ _ _ rfl, rfl⟩

end CanonicalRoots
