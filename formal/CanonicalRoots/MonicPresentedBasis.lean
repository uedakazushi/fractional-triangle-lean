import CanonicalRoots.AmbientBasis
import CanonicalRoots.Target

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- An arbitrary hypersurface which is a pure monic power in its first variable. -/
def separatedRelation {n : ℕ} (k : ℕ) (g : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ := X 0 ^ k + rename Fin.succ g

theorem finSuccEquiv_separatedRelation {n : ℕ} (k : ℕ) (g : MvPolynomial (Fin n) ℂ) :
    finSuccEquiv ℂ n (separatedRelation k g) = Polynomial.X ^ k + Polynomial.C g := by
  simp [separatedRelation, finSuccEquiv_X_zero]
  induction g using MvPolynomial.induction_on with
  | C c => simp [finSuccEquiv_apply]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf, finSuccEquiv_X_succ]

def separatedAdjoinEquiv {n : ℕ} (k : ℕ) (g : MvPolynomial (Fin n) ℂ) :
    PresentedRing (separatedRelation k g) ≃ₐ[ℂ]
      AdjoinRoot (Polynomial.X ^ k + Polynomial.C g) :=
  Ideal.quotientEquivAlg _ _ (finSuccEquiv ℂ n) (by
    simp [Ideal.map_span, Set.image_singleton, finSuccEquiv_separatedRelation])

theorem separatedAdjoinEquiv_mk {n : ℕ} (k : ℕ) (g : MvPolynomial (Fin n) ℂ)
    (f : MvPolynomial (Fin (n + 1)) ℂ) :
    separatedAdjoinEquiv k g ((Ideal.Quotient.mkₐ ℂ (Ideal.span {separatedRelation k g})) f) =
      AdjoinRoot.mk (Polynomial.X ^ k + Polynomial.C g) (finSuccEquiv ℂ n f) := rfl

def separatedPowerBasis {n : ℕ} (k : ℕ) (hk : 0 < k) (g : MvPolynomial (Fin n) ℂ) :
    Module.Basis (Fin k) (MvPolynomial (Fin n) ℂ)
      (AdjoinRoot (Polynomial.X ^ k + Polynomial.C g)) :=
  (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_add_C g (ne_of_gt hk))).basis.reindex
    (finCongr Polynomial.natDegree_X_pow_add_C)

theorem separatedPowerBasis_apply {n : ℕ} (k : ℕ) (hk : 0 < k)
    (g : MvPolynomial (Fin n) ℂ) (i : Fin k) :
    separatedPowerBasis k hk g i = AdjoinRoot.root (Polynomial.X ^ k + Polynomial.C g) ^ (i : ℕ) := by
  simp [separatedPowerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- The full monomial basis of this actual quotient, with the first exponent bounded. -/
def separatedMonomialBasis {n : ℕ} (k : ℕ) (hk : 0 < k) (g : MvPolynomial (Fin n) ℂ) :
    Module.Basis ((Fin n →₀ ℕ) × Fin k) ℂ (PresentedRing (separatedRelation k g)) :=
  ((basisMonomials (Fin n) ℂ).smulTower (separatedPowerBasis k hk g)).map
    (separatedAdjoinEquiv k g).symm.toLinearEquiv

theorem separatedMonomialBasis_apply {n : ℕ} (k : ℕ) (hk : 0 < k)
    (g : MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) (i : Fin k) :
    separatedMonomialBasis k hk g (d,i) =
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {separatedRelation k g})) (monomial (d.cons i) 1) := by
  apply (separatedAdjoinEquiv k g).injective
  simp only [separatedMonomialBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, Module.Basis.smulTower_apply, coe_basisMonomials,
    separatedPowerBasis_apply, separatedAdjoinEquiv_mk, finSuccEquiv_monomial_cons]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.of,
    RingHom.comp_apply, map_mul, map_pow, AdjoinRoot.mk_X]

end CanonicalRoots
