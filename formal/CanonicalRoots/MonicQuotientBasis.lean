import CanonicalRoots.BoundedMonomialBasis

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Isolating the first variable identifies any principal quotient with its adjoin-root model. -/
def presentedAdjoinEquiv {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ) :
    PresentedRing f ≃ₐ[ℂ] AdjoinRoot (finSuccEquiv ℂ n f) :=
  Ideal.quotientEquivAlg _ _ (finSuccEquiv ℂ n) (by
    simp [Ideal.map_span, Set.image_singleton])

theorem presentedAdjoinEquiv_mk {n : ℕ} (f g : MvPolynomial (Fin (n + 1)) ℂ) :
    presentedAdjoinEquiv f ((Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) g) =
      AdjoinRoot.mk (finSuccEquiv ℂ n f) (finSuccEquiv ℂ n g) := rfl

def monicAdjoinPowerBasis {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) :
    Module.Basis (Fin (finSuccEquiv ℂ n f).natDegree) (MvPolynomial (Fin n) ℂ)
      (AdjoinRoot (finSuccEquiv ℂ n f)) :=
  (AdjoinRoot.powerBasis' hf).basis

theorem monicAdjoinPowerBasis_apply {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) (i : Fin (finSuccEquiv ℂ n f).natDegree) :
    monicAdjoinPowerBasis f hf i = AdjoinRoot.root (finSuccEquiv ℂ n f) ^ (i : ℕ) := by
  exact PowerBasis.basis_eq_pow _ _

/-- The monic quotient basis also permits terms of smaller positive degree in the eliminated variable. -/
def monicQuotientMonomialBasis {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) :
    Module.Basis ((Fin n →₀ ℕ) × Fin (finSuccEquiv ℂ n f).natDegree) ℂ (PresentedRing f) :=
  ((basisMonomials (Fin n) ℂ).smulTower (monicAdjoinPowerBasis f hf)).map
    (presentedAdjoinEquiv f).symm.toLinearEquiv

theorem monicQuotientMonomialBasis_apply {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) (d : Fin n →₀ ℕ)
    (i : Fin (finSuccEquiv ℂ n f).natDegree) :
    monicQuotientMonomialBasis f hf (d,i) =
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) (monomial (d.cons i) 1) := by
  apply (presentedAdjoinEquiv f).injective
  simp only [monicQuotientMonomialBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, Module.Basis.smulTower_apply, coe_basisMonomials,
    monicAdjoinPowerBasis_apply, presentedAdjoinEquiv_mk, finSuccEquiv_monomial_cons]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.of,
    RingHom.comp_apply, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.powerBasis'_gen]

def monicQuotientBoundedBasis {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) :
    Module.Basis {d : Fin (n + 1) →₀ ℕ // d 0 < (finSuccEquiv ℂ n f).natDegree} ℂ
      (PresentedRing f) :=
  (monicQuotientMonomialBasis f hf).reindex (boundedMonomialIndexEquiv n _)

theorem monicQuotientBoundedBasis_apply {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic)
    (d : {d : Fin (n + 1) →₀ ℕ // d 0 < (finSuccEquiv ℂ n f).natDegree}) :
    monicQuotientBoundedBasis f hf d =
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) (monomial d.val 1) := by
  rw [monicQuotientBoundedBasis, Module.Basis.reindex_apply]
  change monicQuotientMonomialBasis f hf (d.val.tail, ⟨d.val 0,d.property⟩) = _
  rw [monicQuotientMonomialBasis_apply, Finsupp.cons_tail]

theorem monicQuotientMonomials_span {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) :
    Submodule.span ℂ (Set.range (fun d : {d : Fin (n + 1) →₀ ℕ // d 0 < (finSuccEquiv ℂ n f).natDegree} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) (monomial d.val 1))) = ⊤ := by
  have hh : (fun d : {d : Fin (n + 1) →₀ ℕ // d 0 < (finSuccEquiv ℂ n f).natDegree} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) (monomial d.val 1)) =
      monicQuotientBoundedBasis f hf := funext fun d => (monicQuotientBoundedBasis_apply f hf d).symm
  rw [hh]
  exact Module.Basis.span_eq _

def monicQuotientPermutedBoundedBasis {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) (e : Equiv.Perm (Fin (n + 1))) :
    Module.Basis {d : Fin (n + 1) →₀ ℕ // d (e 0) < (finSuccEquiv ℂ n f).natDegree} ℂ
      (PresentedRing (rename e f)) :=
  ((monicQuotientBoundedBasis f hf).map (presentedRenameEquiv f e).toLinearEquiv).reindex
    (boundedExponentRename _ e)

theorem monicQuotientPermutedBoundedBasis_apply {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) (e : Equiv.Perm (Fin (n + 1)))
    (d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < (finSuccEquiv ℂ n f).natDegree}) :
    monicQuotientPermutedBoundedBasis f hf e d =
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename e f})) (monomial d.val 1) := by
  obtain ⟨b,rfl⟩ := (boundedExponentRename (finSuccEquiv ℂ n f).natDegree e).surjective d
  rw [monicQuotientPermutedBoundedBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, monicQuotientBoundedBasis_apply,
    presentedRenameEquiv_mk, rename_monomial]
  simp [boundedExponentRename, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]

theorem monicQuotientPermutedMonomials_span {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (hf : (finSuccEquiv ℂ n f).Monic) (e : Equiv.Perm (Fin (n + 1))) :
    Submodule.span ℂ (Set.range (fun d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < (finSuccEquiv ℂ n f).natDegree} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename e f})) (monomial d.val 1))) = ⊤ := by
  have hh : (fun d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < (finSuccEquiv ℂ n f).natDegree} =>
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename e f})) (monomial d.val 1)) =
      monicQuotientPermutedBoundedBasis f hf e :=
    funext fun d => (monicQuotientPermutedBoundedBasis_apply f hf e d).symm
  rw [hh]
  exact Module.Basis.span_eq _

end CanonicalRoots
