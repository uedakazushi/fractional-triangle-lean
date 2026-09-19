import Mathlib

/- Independent semantic definitions: this file imports no enumerator. -/
noncomputable section
namespace CanonicalRoots
open MvPolynomial

abbrev FreeDegrees (n : ℕ) := Option (Fin n) → ℤ

def degreeRelations {n : ℕ} (p : Fin n → ℕ) : AddSubgroup (FreeDegrees n) :=
  AddSubgroup.closure (Set.range fun i : Fin n =>
    (p i : ℤ) • Pi.single (some i) 1 - Pi.single none 1)

abbrev DegreeGroup {n : ℕ} (p : Fin n → ℕ) := FreeDegrees n ⧸ degreeRelations p

def xDegree {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : DegreeGroup p :=
  QuotientAddGroup.mk' (degreeRelations p) (Pi.single (some i) 1)

def cDegree {n : ℕ} (p : Fin n → ℕ) : DegreeGroup p :=
  QuotientAddGroup.mk' (degreeRelations p) (Pi.single none 1)

def omegaDegree {n : ℕ} (p : Fin n → ℕ) : DegreeGroup p :=
  cDegree p - ∑ i, xDegree p i

def IsCanonicalRoot {n : ℕ} (p : Fin n → ℕ) (a : ℕ) (τ : DegreeGroup p) : Prop :=
  a • τ = omegaDegree p

def AdmissibleSignature {n : ℕ} (p : Fin n → ℕ) : Prop :=
  (∀ i, 2 ≤ p i) ∧ (∑ i, (1 : ℚ) / p i) < 1

def fermat {n : ℕ} (p : Fin n → ℕ) : MvPolynomial (Fin n) ℂ :=
  ∑ i, X i ^ p i

def fermatIdeal {n : ℕ} (p : Fin n → ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span {fermat p}

abbrev AmbientRing {n : ℕ} (p : Fin n → ℕ) :=
  MvPolynomial (Fin n) ℂ ⧸ fermatIdeal p

def ambientQuotient {n : ℕ} (p : Fin n → ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] AmbientRing p :=
  Ideal.Quotient.mkₐ ℂ (fermatIdeal p)

def ambientPiece {n : ℕ} (p : Fin n → ℕ) (l : DegreeGroup p) :
    Submodule ℂ (AmbientRing p) :=
  (weightedHomogeneousSubmodule ℂ (xDegree p) l).map (ambientQuotient p).toLinearMap

def rootModule {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :
    Submodule ℂ (AmbientRing p) := ⨆ m : ℕ, ambientPiece p (m • τ)

theorem ambientPiece_mul {n : ℕ} (p : Fin n → ℕ) {l k : DegreeGroup p}
    {x y : AmbientRing p} (hx : x ∈ ambientPiece p l) (hy : y ∈ ambientPiece p k) :
    x * y ∈ ambientPiece p (l + k) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  exact Submodule.mem_map.mpr ⟨f * g, hf.mul hg, (ambientQuotient p).map_mul f g⟩

theorem rootModule_mul {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    {x y : AmbientRing p} (hx : x ∈ rootModule p τ) (hy : y ∈ rootModule p τ) :
    x * y ∈ rootModule p τ := by
  refine Submodule.iSup_induction (fun m : ℕ => ambientPiece p (m • τ))
    (motive := fun x => x * y ∈ rootModule p τ) hx
    (fun i x hx => ?_) ?_ (fun x z hx hz => ?_)
  · refine Submodule.iSup_induction (fun m : ℕ => ambientPiece p (m • τ))
      (motive := fun y => x * y ∈ rootModule p τ) hy
      (fun j y hy => ?_) ?_ (fun y z hy hz => ?_)
    · exact (le_iSup (fun m : ℕ => ambientPiece p (m • τ)) (i+j))
        (by simpa [add_nsmul] using ambientPiece_mul p hx hy)
    · simpa using (rootModule p τ).zero_mem
    · simpa [mul_add] using (rootModule p τ).add_mem hy hz
  · simpa using (rootModule p τ).zero_mem
  · simpa [add_mul] using (rootModule p τ).add_mem hx hz

theorem rootModule_algebraMap {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (c : ℂ) :
    algebraMap ℂ (AmbientRing p) c ∈ rootModule p τ := by
  apply (le_iSup (fun m : ℕ => ambientPiece p (m • τ)) 0)
  apply Submodule.mem_map.mpr
  refine ⟨C c, ?_, ?_⟩
  · simpa using isWeightedHomogeneous_C (xDegree p) c
  · exact (ambientQuotient p).commutes c

/-- The actual subalgebra consisting of finite sums of T_(mτ), m ≥ 0. -/
def rootSubalgebra {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) :
    Subalgebra ℂ (AmbientRing p) where
  carrier := rootModule p τ
  zero_mem' := (rootModule p τ).zero_mem
  one_mem' := by simpa using rootModule_algebraMap p τ 1
  add_mem' := (rootModule p τ).add_mem
  mul_mem' := rootModule_mul p τ
  algebraMap_mem' := rootModule_algebraMap p τ

abbrev RootRing {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) := rootSubalgebra p τ

def rootPiece {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p) (m : ℕ) :
    Submodule ℂ (RootRing p τ) :=
  (ambientPiece p (m • τ)).comap (rootSubalgebra p τ).val.toLinearMap

/-- A concrete graded algebra equivalence, retaining the underlying algebra equivalence. -/
structure GradedAlgEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (s : ℕ → Submodule ℂ A) (t : ℕ → Submodule ℂ B)
    extends A ≃ₐ[ℂ] B where
  preserves : ∀ m x, x ∈ s m ↔ toAlgEquiv x ∈ t m

def IsolatedAtOrigin {n : ℕ} (f : MvPolynomial (Fin n) ℂ) : Prop :=
  ∀ z : Fin n → ℂ, (∀ i, eval z (pderiv i f) = 0) ↔ z = 0

def HasNoConstantOrLinear {n : ℕ} (f : MvPolynomial (Fin n) ℂ) : Prop :=
  f.coeff 0 = 0 ∧ ∀ i, f.coeff (Finsupp.single i 1) = 0

theorem fermat_pderiv {n : ℕ} (p : Fin n → ℕ) (i : Fin n) :
    pderiv i (fermat p) = (p i : ℂ) • (X i ^ (p i - 1)) := by
  classical
  simp [fermat, map_sum, Pi.single_apply, smul_eq_C_mul]

theorem fermat_isolated {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i) :
    IsolatedAtOrigin (fermat p) := by
  intro z
  constructor
  · intro hz
    funext i
    have h := hz i
    rw [fermat_pderiv] at h
    have hi : (p i : ℂ) ≠ 0 := by exact_mod_cast (by have := hp i; omega : p i ≠ 0)
    have hpow : z i ^ (p i - 1) = 0 := by
      simpa [hi, smul_eq_C_mul] using h
    exact (pow_eq_zero_iff (by have := hp i; omega)).mp hpow
  · rintro rfl i
    have he : p i - 1 ≠ 0 := by have := hp i; omega
    simp [fermat_pderiv, smul_eq_C_mul, he]

end CanonicalRoots
