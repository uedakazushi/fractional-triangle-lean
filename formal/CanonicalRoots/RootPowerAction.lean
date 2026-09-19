import CanonicalRoots.BasisRegroup

noncomputable section
namespace CanonicalRoots
open MvPolynomial

def powerExponent {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) (d : Fin n →₀ ℕ) :
    Fin (n + 1) →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm (fun i => (u * p i.succ) * d i)).cons 0

def powerSubstitution {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin (n + 1)) ℂ :=
  aeval (fun i => X i.succ ^ (u * p i.succ))

theorem powerSubstitution_monomial {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ)
    (d : Fin n →₀ ℕ) : powerSubstitution p u (monomial d 1) = monomial (powerExponent p u d) 1 := by
  classical
  rw [powerSubstitution, aeval_monomial, map_one, one_mul, monomial_eq, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp [powerExponent, Fin.prod_univ_succ, pow_mul]

theorem rootCoordinatePower_homogeneous {n : ℕ} (p : Fin n → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (i : Fin n) :
    ambientQuotient p (X i ^ (u * p i)) ∈ ambientPiece p (N • τ) := by
  apply Submodule.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  have hd : (u * p i) • xDegree p i = N • τ := by
    rw [mul_nsmul', show p i • xDegree p i = cDegree p from degree_relation p i, hN]
  rw [← hd]
  exact (isWeightedHomogeneous_X ℂ (xDegree p) i).pow _

theorem rootPower_homogeneous {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (i : Fin n) :
    ambientQuotient p (X i.succ ^ (u * p i.succ)) ∈ ambientPiece p (N • τ) :=
  rootCoordinatePower_homogeneous p τ N u hN i.succ

theorem rootPower_mem {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (i : Fin n) :
    ambientQuotient p (X i.succ ^ (u * p i.succ)) ∈ rootModule p τ :=
  (le_iSup (fun m : ℕ => ambientPiece p (m • τ)) N) (rootPower_homogeneous p τ N u hN i)

def rootPowerGenerator {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (i : Fin n) : RootRing p τ :=
  ⟨ambientQuotient p (X i.succ ^ (u * p i.succ)), rootPower_mem p τ N u hN i⟩

theorem rootPowerGenerator_homogeneous {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (i : Fin n) :
    rootPowerGenerator p τ N u hN i ∈ rootPiece p τ N :=
  rootPower_homogeneous p τ N u hN i

def rootPowerHom {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] RootRing p τ :=
  aeval (rootPowerGenerator p τ N u hN)

theorem rootPowerHom_comp_val {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) :
    (rootSubalgebra p τ).val.comp (rootPowerHom p τ N u hN) =
      (ambientQuotient p).comp (powerSubstitution p u) := by
  ext i
  simp [rootPowerHom, rootPowerGenerator, powerSubstitution]

theorem rootPowerHom_monomial {n : ℕ} (p : Fin (n + 1) → ℕ) (τ : DegreeGroup p)
    (N u : ℕ) (hN : N • τ = u • cDegree p) (d : Fin n →₀ ℕ) :
    (rootPowerHom p τ N u hN (monomial d 1) : AmbientRing p) =
      ambientQuotient p (monomial (powerExponent p u d) 1) := by
  have h := AlgHom.congr_fun (rootPowerHom_comp_val p τ N u hN) (monomial d 1)
  simpa [powerSubstitution_monomial] using h

/-- Multiplication by a polynomial monomial gives exactly the corresponding box basis vector. -/
theorem rootPowerHom_mul_box {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (N u : ℕ) (hu : 0 < u) (hN : N • τ = u • cDegree p)
    (d : Fin n →₀ ℕ) (q : RootBox p τ u) :
    rootPowerHom p τ N u hN (monomial d 1) *
      rootPowerBoxBasis p hp ha τ hτ N u hu hN (0, q) =
        rootPowerBoxBasis p hp ha τ hτ N u hu hN (d, q) := by
  apply Subtype.ext
  change (rootPowerHom p τ N u hN (monomial d 1) : AmbientRing p) * _ = _
  rw [rootPowerHom_monomial, rootPowerBoxBasis_apply, rootPowerBoxBasis_apply,
    ambientPowerBoxBasis_zero, boxMonomial, ← map_mul, monomial_mul_monomial, one_mul,
    ambientPowerBoxBasis_apply]
  have he : powerExponent p u d + boxExponent p u q.val =
      (Finsupp.equivFunOnFinite.symm
        (fun i => (u * p i.succ) * d i + (q.val.1 i : ℕ))).cons (q.val.2 : ℕ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [powerExponent, boxExponent]
  rw [he]

end CanonicalRoots
