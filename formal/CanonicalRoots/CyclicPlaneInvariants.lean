import CanonicalRoots.CyclicMonomialEmbedding

noncomputable section
namespace CanonicalRoots
open MvPolynomial

/-- The diagonal action on the actual two-variable polynomial algebra. -/
def cyclicPlaneHom (ζ : ℂˣ) : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  aeval ![C (ζ : ℂ) * X 0, C (↑(ζ⁻¹) : ℂ) * X 1]

def cyclicMonomialValue (ζ : ℂˣ) (d : Fin 2 →₀ ℕ) : ℂ :=
  ↑(ζ ^ d 0 * (ζ⁻¹) ^ d 1)

theorem cyclicPlaneHom_monomial (ζ : ℂˣ) (d : Fin 2 →₀ ℕ) (c : ℂ) :
    cyclicPlaneHom ζ (monomial d c) = cyclicMonomialValue ζ d • monomial d c := by
  rw [cyclicPlaneHom, aeval_monomial, smul_eq_C_mul, monomial_eq]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_succ, cyclicMonomialValue, mul_pow, map_pow]
  rw [← inv_pow (ζ : ℂ) (d 1),
    map_pow (C : ℂ →+* MvPolynomial (Fin 2) ℂ) ((ζ : ℂ)⁻¹) (d 1)]
  ring

theorem cyclicPlaneHom_coeff (ζ : ℂˣ) (f : MvPolynomial (Fin 2) ℂ) (d : Fin 2 →₀ ℕ) :
    (cyclicPlaneHom ζ f).coeff d = cyclicMonomialValue ζ d * f.coeff d := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
      rw [cyclicPlaneHom_monomial, coeff_smul, coeff_monomial]
      by_cases h : e = d
      · subst e; simp
      · simp [h]
  | add f g hf hg => simp [map_add, hf, hg, mul_add]

/-- The finite cyclic invariants, defined by the actual substitution action. -/
def cyclicPlaneFixed (s : ℕ) : Subalgebra ℂ (MvPolynomial (Fin 2) ℂ) where
  carrier := {f | ∀ ζ : rootsOfUnity s ℂ, cyclicPlaneHom ζ.val f = f}
  algebraMap_mem' c ζ := (cyclicPlaneHom ζ.val).commutes c
  zero_mem' ζ := map_zero _
  one_mem' ζ := map_one _
  add_mem' hf hg ζ := by rw [map_add, hf ζ, hg ζ]
  mul_mem' hf hg ζ := by rw [map_mul, hf ζ, hg ζ]

/-- Testing all s-th roots of unity detects the exact residue condition on a monomial. -/
theorem cyclicMonomialValue_all_one_iff (s : ℕ) (hs : 0 < s) (d : Fin 2 →₀ ℕ) :
    (∀ ζ : rootsOfUnity s ℂ, cyclicMonomialValue ζ.val d = 1) ↔ d 0 % s = d 1 % s := by
  have value_eq (ζ : ℂˣ) : cyclicMonomialValue ζ d = 1 ↔ ζ ^ d 0 = ζ ^ d 1 := by
    change ((ζ ^ d 0 * (ζ⁻¹) ^ d 1 : ℂˣ) : ℂ) = (1 : ℂˣ) ↔ _
    rw [Units.val_inj, inv_pow, mul_inv_eq_one]
  constructor
  · intro h
    let hr := Complex.isPrimitiveRoot_exp s (ne_of_gt hs)
    let ζ : ℂˣ := (hr.isUnit (ne_of_gt hs)).unit
    have hprim : IsPrimitiveRoot ζ s := hr.isUnit_unit (ne_of_gt hs)
    have hz := (value_eq ζ).mp (h ⟨ζ, (mem_rootsOfUnity _ _).mpr hprim.pow_eq_one⟩)
    apply hprim.pow_inj (Nat.mod_lt _ hs) (Nat.mod_lt _ hs)
    simpa only [← pow_eq_pow_mod (d 0) hprim.pow_eq_one,
      ← pow_eq_pow_mod (d 1) hprim.pow_eq_one] using hz
  · intro hd ζ
    apply (value_eq ζ.val).mpr
    have hζ := (mem_rootsOfUnity s ζ.val).mp ζ.property
    rw [pow_eq_pow_mod (d 0) hζ, pow_eq_pow_mod (d 1) hζ, hd]

theorem mem_cyclicPlaneFixed_iff (s : ℕ) (hs : 0 < s) (f : MvPolynomial (Fin 2) ℂ) :
    f ∈ cyclicPlaneFixed s ↔ ∀ d, f.coeff d ≠ 0 → d 0 % s = d 1 % s := by
  constructor
  · intro hf d hd
    apply (cyclicMonomialValue_all_one_iff s hs d).mp
    intro ζ
    have he := congrArg (fun f : MvPolynomial (Fin 2) ℂ => f.coeff d) (hf ζ)
    rw [cyclicPlaneHom_coeff] at he
    exact mul_right_cancel₀ hd (he.trans (one_mul _).symm)
  · intro hf ζ
    apply MvPolynomial.ext
    intro d
    rw [cyclicPlaneHom_coeff]
    by_cases hd : f.coeff d = 0
    · rw [hd, mul_zero]
    · rw [(cyclicMonomialValue_all_one_iff s hs d).mpr (hf d hd) ζ, one_mul]

/-- The quotient presentation is identified with the full fixed algebra, not just its generators. -/
theorem cyclicQuotientMap_range_eq_fixed (s : ℕ) (hs : 0 < s) :
    (cyclicQuotientMap s).range = cyclicPlaneFixed s := by
  apply Subalgebra.ext
  intro f
  rw [mem_cyclicQuotientMap_range_iff s hs, mem_cyclicPlaneFixed_iff s hs]

/-- The actual complex algebra isomorphism C[U,V,W]/(UV-W^s) ≃ C[x,y]^μ_s. -/
def cyclicQuotientEquivFixed (s : ℕ) (hs : 0 < s) : CyclicModelRing s ≃ₐ[ℂ] cyclicPlaneFixed s :=
  (AlgEquiv.ofInjective (cyclicQuotientMap s) (cyclicQuotientMap_injective s hs)).trans
    (Subalgebra.equivOfEq _ _ (cyclicQuotientMap_range_eq_fixed s hs))

end CanonicalRoots
