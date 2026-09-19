import CanonicalRoots.MonicPresentedBasis
import CanonicalRoots.AmbientReindex

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def boundedMonomialIndexEquiv (n k : ℕ) :
    ((Fin n →₀ ℕ) × Fin k) ≃ {d : Fin (n + 1) →₀ ℕ // d 0 < k} where
  toFun q := ⟨q.1.cons (q.2 : ℕ), by simpa using q.2.isLt⟩
  invFun d := (d.val.tail, ⟨d.val 0, d.property⟩)
  left_inv q := by rcases q with ⟨d,i⟩; simp
  right_inv d := Subtype.ext (Finsupp.cons_tail d.val)

def boundedExponentRename {n : ℕ} (k : ℕ) (e : Equiv.Perm (Fin (n + 1))) :
    {d : Fin (n + 1) →₀ ℕ // d 0 < k} ≃
      {d : Fin (n + 1) →₀ ℕ // d (e 0) < k} :=
  (Finsupp.domCongr e).toEquiv.subtypeEquiv (by
    intro d
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.mapDomain_apply_of_injective e.injective])

def separatedBoundedBasis {n : ℕ} (k : ℕ) (hk : 0 < k) (g : MvPolynomial (Fin n) ℂ) :
    Module.Basis {d : Fin (n + 1) →₀ ℕ // d 0 < k} ℂ (PresentedRing (separatedRelation k g)) :=
  (separatedMonomialBasis k hk g).reindex (boundedMonomialIndexEquiv n k)

theorem separatedBoundedBasis_apply {n : ℕ} (k : ℕ) (hk : 0 < k)
    (g : MvPolynomial (Fin n) ℂ) (d : {d : Fin (n + 1) →₀ ℕ // d 0 < k}) :
    separatedBoundedBasis k hk g d =
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {separatedRelation k g})) (monomial d.val 1) := by
  rw [separatedBoundedBasis, Module.Basis.reindex_apply]
  change separatedMonomialBasis k hk g (d.val.tail, ⟨d.val 0,d.property⟩) = _
  rw [separatedMonomialBasis_apply, Finsupp.cons_tail]

def ambientBoundedBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0) :
    Module.Basis {d : Fin (n + 1) →₀ ℕ // d 0 < p 0} ℂ (AmbientRing p) :=
  (ambientMonomialBasis p hp).reindex (boundedMonomialIndexEquiv n (p 0))

theorem ambientBoundedBasis_apply {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : 0 < p 0)
    (d : {d : Fin (n + 1) →₀ ℕ // d 0 < p 0}) :
    ambientBoundedBasis p hp d = ambientQuotient p (monomial d.val 1) := by
  rw [ambientBoundedBasis, Module.Basis.reindex_apply]
  change ambientMonomialBasis p hp (d.val.tail, ⟨d.val 0,d.property⟩) = _
  rw [ambientMonomialBasis_apply, Finsupp.cons_tail]

/-- The actual Fermat basis can eliminate any chosen coordinate by a permutation. -/
def ambientPermutedBoundedBasis {n : ℕ} (p : Fin (n + 1) → ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (hp : 0 < p (e 0)) :
    Module.Basis {d : Fin (n + 1) →₀ ℕ // d (e 0) < p (e 0)} ℂ (AmbientRing p) :=
  ((ambientBoundedBasis (fun i => p (e i)) hp).map (ambientReindex p e).toLinearEquiv).reindex
    (boundedExponentRename (p (e 0)) e)

theorem ambientPermutedBoundedBasis_apply {n : ℕ} (p : Fin (n + 1) → ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (hp : 0 < p (e 0))
    (d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < p (e 0)}) :
    ambientPermutedBoundedBasis p e hp d = ambientQuotient p (monomial d.val 1) := by
  obtain ⟨b,rfl⟩ := (boundedExponentRename (p (e 0)) e).surjective d
  rw [ambientPermutedBoundedBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    ambientBoundedBasis_apply, ambientReindex_quotient, rename_monomial]
  simp [boundedExponentRename, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]

/-- Permuting variables transports the actual principal quotient. -/
def presentedRenameEquiv {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (e : Equiv.Perm (Fin n)) :
    PresentedRing f ≃ₐ[ℂ] PresentedRing (rename e f) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv ℂ e) (by
    simp [Ideal.map_span, Set.image_singleton])

theorem presentedRenameEquiv_mk {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (e : Equiv.Perm (Fin n)) (g : MvPolynomial (Fin n) ℂ) :
    presentedRenameEquiv f e ((Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) g) =
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename e f})) (rename e g) := rfl

def separatedPermutedBoundedBasis {n : ℕ} (k : ℕ) (hk : 0 < k)
    (g : MvPolynomial (Fin n) ℂ) (e : Equiv.Perm (Fin (n + 1))) :
    Module.Basis {d : Fin (n + 1) →₀ ℕ // d (e 0) < k} ℂ
      (PresentedRing (rename e (separatedRelation k g))) :=
  ((separatedBoundedBasis k hk g).map (presentedRenameEquiv (separatedRelation k g) e).toLinearEquiv).reindex
    (boundedExponentRename k e)

theorem separatedPermutedBoundedBasis_apply {n : ℕ} (k : ℕ) (hk : 0 < k)
    (g : MvPolynomial (Fin n) ℂ) (e : Equiv.Perm (Fin (n + 1)))
    (d : {d : Fin (n + 1) →₀ ℕ // d (e 0) < k}) :
    separatedPermutedBoundedBasis k hk g e d =
      (Ideal.Quotient.mkₐ ℂ (Ideal.span {rename e (separatedRelation k g)})) (monomial d.val 1) := by
  obtain ⟨b,rfl⟩ := (boundedExponentRename k e).surjective d
  rw [separatedPermutedBoundedBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, separatedBoundedBasis_apply,
    presentedRenameEquiv_mk, rename_monomial]
  simp [boundedExponentRename, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]

end CanonicalRoots
