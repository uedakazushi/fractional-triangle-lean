import CanonicalRoots.RootHilbert

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- Simultaneous Euclidean division of all exponents. -/
def exponentBoxEquiv {n : ℕ} (P : Fin n → ℕ) (hP : ∀ i, 0 < P i) :
    (Fin n →₀ ℕ) ≃ (Fin n →₀ ℕ) × (∀ i, Fin (P i)) where
  toFun d := (Finsupp.equivFunOnFinite.symm (fun i => d i / P i),
    fun i => ⟨d i % P i, Nat.mod_lt _ (hP i)⟩)
  invFun q := Finsupp.equivFunOnFinite.symm (fun i => P i * q.1 i + q.2 i)
  left_inv d := by
    ext i
    exact Nat.div_add_mod _ _
  right_inv q := by
    apply Prod.ext
    · ext i
      change (P i * q.1 i + (q.2 i : ℕ)) / P i = q.1 i
      rw [Nat.mul_add_div (hP i), Nat.div_eq_of_lt (q.2 i).isLt, add_zero]
    · funext i
      apply Fin.ext
      change (P i * q.1 i + (q.2 i : ℕ)) % P i = (q.2 i : ℕ)
      simp [Nat.mod_eq_of_lt (q.2 i).isLt]

/-- Finite exponent box for powers X_{i+1}^{u p_{i+1}} in the monic quotient. -/
abbrev AmbientBox {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) :=
  (∀ i : Fin n, Fin (u * p i.succ)) × Fin (p 0)

def boxExponent {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) (q : AmbientBox p u) :
    Fin (n + 1) →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm (fun i => (q.1 i : ℕ))).cons (q.2 : ℕ)

def boxDegree {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) (q : AmbientBox p u) : DegreeGroup p :=
  Finsupp.weight (xDegree p) (boxExponent p u q)

def boxMonomial {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) (q : AmbientBox p u) : AmbientRing p :=
  ambientQuotient p (monomial (boxExponent p u q) 1)

def ambientPowerBoxIndexEquiv {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (u : ℕ) (hu : 0 < u) :
    ((Fin n →₀ ℕ) × Fin (p 0)) ≃ ((Fin n →₀ ℕ) × AmbientBox p u) :=
  ((exponentBoxEquiv (fun i => u * p i.succ) (fun i => Nat.mul_pos hu (hp i.succ))).prodCongr
    (Equiv.refl (Fin (p 0)))).trans (Equiv.prodAssoc _ _ _)

/-- Regrouping the actual quotient basis by the finite exponent box. -/
def ambientPowerBoxBasis {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (u : ℕ) (hu : 0 < u) :
    Module.Basis ((Fin n →₀ ℕ) × AmbientBox p u) ℂ (AmbientRing p) :=
  (ambientMonomialBasis p (hp 0)).reindex (ambientPowerBoxIndexEquiv p hp u hu)

theorem ambientPowerBoxBasis_apply {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (u : ℕ) (hu : 0 < u) (d : Fin n →₀ ℕ) (q : AmbientBox p u) :
    ambientPowerBoxBasis p hp u hu (d, q) = ambientQuotient p
      (monomial ((Finsupp.equivFunOnFinite.symm
        (fun i => (u * p i.succ) * d i + (q.1 i : ℕ))).cons (q.2 : ℕ)) 1) := by
  simp only [ambientPowerBoxBasis, Module.Basis.reindex_apply]
  exact ambientMonomialBasis_apply p (hp 0) _ _

theorem ambientPowerBoxBasis_zero {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (u : ℕ) (hu : 0 < u) (q : AmbientBox p u) :
    ambientPowerBoxBasis p hp u hu (0, q) = boxMonomial p u q := by
  rw [ambientPowerBoxBasis_apply]
  simp [boxMonomial, boxExponent]

theorem boxMonomial_homogeneous {n : ℕ} (p : Fin (n + 1) → ℕ)
    (u : ℕ) (q : AmbientBox p u) : boxMonomial p u q ∈ ambientPiece p (boxDegree p u q) :=
  Submodule.mem_map.mpr ⟨_, isWeightedHomogeneous_monomial _ _ _ rfl, rfl⟩

/-- Reversing every exponent is an involution of the finite box. -/
def boxComplement {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) : AmbientBox p u ≃ AmbientBox p u where
  toFun q := (fun i => (q.1 i).rev, q.2.rev)
  invFun q := (fun i => (q.1 i).rev, q.2.rev)
  left_inv q := by simp
  right_inv q := by simp

theorem boxDegree_expression {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) (q : AmbientBox p u) :
    boxDegree p u q = (q.2 : ℤ) • xDegree p 0 + ∑ i, (q.1 i : ℤ) • xDegree p i.succ := by
  simp [boxDegree, boxExponent, Finsupp.weight_eq_sum, Fin.sum_univ_succ]

/-- Complementary monomials add to the anticanonical top degree in the full degree group. -/
theorem boxDegree_complement {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ) (q : AmbientBox p u) :
    boxDegree p u q + boxDegree p u (boxComplement p u q) =
      omegaDegree p + (n * u) • cDegree p := by
  have hz : (q.2 : ℤ) + (q.2.rev : ℤ) = (p 0 : ℤ) - 1 := by
    simp only [Fin.val_rev]
    have := q.2.isLt
    omega
  have hs : ∀ i, (q.1 i : ℤ) + ((q.1 i).rev : ℤ) = (u * p i.succ : ℕ) - (1 : ℤ) := by
    intro i
    simp only [Fin.val_rev]
    have := (q.1 i).isLt
    omega
  calc
    _ = ((q.2 : ℤ) + (q.2.rev : ℤ)) • xDegree p 0 +
        ∑ i, ((q.1 i : ℤ) + ((q.1 i).rev : ℤ)) • xDegree p i.succ := by
      simp only [boxDegree_expression, boxComplement, Equiv.coe_fn_mk, add_zsmul,
        Finset.sum_add_distrib]
      abel
    _ = ((p 0 : ℤ) - 1) • xDegree p 0 +
        ∑ i : Fin n, ((u * p i.succ : ℕ) - (1 : ℤ)) • xDegree p i.succ := by rw [hz]; simp only [hs]
    _ = (cDegree p - xDegree p 0) + ∑ i : Fin n, (u • cDegree p - xDegree p i.succ) := by
      simp only [sub_zsmul, one_zsmul, Nat.cast_mul, mul_smul, degree_relation]
      simp only [natCast_zsmul, sub_eq_add_neg]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        omegaDegree, Fin.sum_univ_succ, Nat.mul_comm n u, mul_nsmul]
      abel

theorem powerBoxDegree {n : ℕ} (p : Fin (n + 1) → ℕ) (u : ℕ)
    (d : Fin n →₀ ℕ) (q : AmbientBox p u) :
    Finsupp.weight (xDegree p) ((Finsupp.equivFunOnFinite.symm
      (fun i => (u * p i.succ) * d i + (q.1 i : ℕ))).cons (q.2 : ℕ)) =
        boxDegree p u q + (∑ i, d i) • (u • cDegree p) := by
  have hi : ∀ i : Fin n, ((u * p i.succ) * d i) • xDegree p i.succ =
      d i • (u • cDegree p) := by
    intro i
    have he : ((u * p i.succ) * d i) • xDegree p i.succ =
        d i • (u • (p i.succ • xDegree p i.succ)) := by
      simp only [← mul_nsmul]
      congr 1
      ring
    rw [he]
    rw [show p i.succ • xDegree p i.succ = cDegree p from degree_relation p i.succ]
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    Finsupp.coe_equivFunOnFinite_symm, add_nsmul, hi, Finset.sum_add_distrib,
    Finset.sum_nsmul_assoc, boxDegree_expression, natCast_zsmul]
  abel

end CanonicalRoots
