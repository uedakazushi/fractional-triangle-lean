import CanonicalRoots.CoxDegrees

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- A sufficient criterion for the actual root subalgebra to be the entire ambient ring. -/
theorem root_eq_top_of_degrees {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (w : Fin n → ℕ) (hw : ∀ i, xDegree p i = w i • τ) :
    rootSubalgebra p τ = ⊤ := by
  apply top_unique
  intro t ht
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (fermatIdeal p) t
  clear ht
  change ambientQuotient p f ∈ rootSubalgebra p τ
  induction f using MvPolynomial.induction_on with
  | C c => exact rootModule_algebraMap p τ c
  | add f g hf hg => simpa using (rootSubalgebra p τ).add_mem hf hg
  | mul_X f i hf =>
    have hi : ambientQuotient p (X i) ∈ rootSubalgebra p τ := by
      apply (le_iSup (fun m : ℕ => ambientPiece p (m • τ)) (w i))
      apply Submodule.mem_map.mpr
      exact ⟨X i, by rw [← hw i]; exact isWeightedHomogeneous_X ℂ (xDegree p) i, rfl⟩
    simpa using (rootSubalgebra p τ).mul_mem hf hi

/-- An algebra isomorphism built from equality of the actual subalgebra with the ambient ring. -/
def rootAmbientEquiv {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (w : Fin n → ℕ) (hw : ∀ i, xDegree p i = w i • τ) :
    RootRing p τ ≃ₐ[ℂ] AmbientRing p :=
  (Subalgebra.equivOfEq _ _ (root_eq_top_of_degrees p τ w hw)).trans Subalgebra.topEquiv

/-- General integer certificate, with no assumption that the degree group is torsion free. -/
theorem degree_certificate {n : ℕ} (p : Fin n → ℕ) (i : Fin n) (w : ℤ)
    (C : Fin n → ℤ) (hC : ∑ j, C j = w)
    (hcol : ∀ j, (p j : ℤ)*C j = (if j=i then 1 else 0)+w) :
    xDegree p i = w • omegaDegree p := by
  have hs : ∑ j, (C j • ((p j : ℤ) • xDegree p j) - w • xDegree p j) = xDegree p i := by
    have hterm : ∀ j, C j • ((p j : ℤ) • xDegree p j) - w • xDegree p j =
        if j=i then xDegree p i else 0 := by
      intro j
      rw [← mul_smul, mul_comm, hcol, add_zsmul]
      split_ifs with h
      · subst j; simp
      · simp
    simp only [hterm]
    simp
  rw [← hs, omegaDegree, zsmul_sub]
  simp only [degree_relation, Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_zsmul, hC]

def exampleSignature : Fin 4 → ℕ := ![2,3,7,43]
def exampleWeights : Fin 4 → ℕ := ![903,602,258,42]

def exampleDegreeCertificate : Matrix (Fin 4) (Fin 4) ℤ :=
  !![452,301,129,21; 301,201,86,14; 129,86,37,6; 21,14,6,1]

theorem example_generator_degrees (i : Fin 4) :
    xDegree exampleSignature i = exampleWeights i • omegaDegree exampleSignature := by
  have h := degree_certificate exampleSignature i (exampleWeights i : ℤ)
    (exampleDegreeCertificate i)
    (by fin_cases i <;> norm_num [exampleDegreeCertificate, exampleWeights, Fin.sum_univ_succ])
    (by intro j; fin_cases i <;> fin_cases j <;>
      norm_num [exampleDegreeCertificate, exampleWeights, exampleSignature])
  simpa using h

theorem example_root_is_actual_ambient :
    rootSubalgebra exampleSignature (omegaDegree exampleSignature) = ⊤ :=
  root_eq_top_of_degrees _ _ exampleWeights example_generator_degrees

def example_root_equiv : RootRing exampleSignature (omegaDegree exampleSignature) ≃ₐ[ℂ]
    AmbientRing exampleSignature :=
  rootAmbientEquiv _ _ exampleWeights example_generator_degrees

theorem example_signature_admissible : AdmissibleSignature exampleSignature := by
  constructor
  · intro i; fin_cases i <;> norm_num [exampleSignature]
  · norm_num [exampleSignature, Fin.sum_univ_succ]

theorem example_is_canonical_root :
    IsCanonicalRoot exampleSignature 1 (omegaDegree exampleSignature) := by
  simp [IsCanonicalRoot]

theorem example_isolated : IsolatedAtOrigin (fermat exampleSignature) :=
  fermat_isolated _ example_signature_admissible.1

end CanonicalRoots
