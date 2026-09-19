import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
namespace CanonicalRoots
open Function

variable {R ι : Type*} [CommRing R] [Fintype ι] (J : ι → Ideal R)
  (hJ : Pairwise (IsCoprime on J))

include hJ in
theorem finite_coprime_iInf_eq_prod : (⨅ i, J i) = ∏ i, J i := by
  classical
  symm
  simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := J) (fun i _ j _ hij => hJ hij)

include hJ in
theorem finite_coprime_iInf_pow (n : ℕ) : (⨅ i, J i) ^ n = ⨅ i, J i ^ n := by
  rw [finite_coprime_iInf_eq_prod J hJ,
    finite_coprime_iInf_eq_prod (fun i => J i ^ n) (fun _ _ hij => (hJ hij).pow)]
  exact (Finset.prod_pow _ _ _).symm

/-- Chinese remainder for the exact finite quotients defining these adic completions. -/
def adicChineseQuotientEquiv (n : ℕ) :
    (R ⧸ ((⨅ i, J i) ^ n • ⊤ : Ideal R)) ≃ₐ[R]
      (∀ i, R ⧸ (J i ^ n • ⊤ : Ideal R)) :=
  (Ideal.quotientEquivAlgOfEq R (by
    simp only [Ideal.smul_eq_mul, Ideal.mul_top]
    exact finite_coprime_iInf_pow J hJ n)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient (fun i => (J i ^ n • ⊤ : Ideal R))
        (by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
          (show Pairwise (IsCoprime on (fun i => J i ^ n)) from fun _ _ hij => (hJ hij).pow))
      commutes' _ := rfl }

theorem adicChineseQuotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : R ⧸ ((⨅ i, J i) ^ n • ⊤ : Ideal R)) (i : ι) :
    adicChineseQuotientEquiv J hJ m (AdicCompletion.transitionMap (⨅ i, J i) R h x) i =
      AdicCompletion.transitionMap (J i) R h (adicChineseQuotientEquiv J hJ n x i) := by
  induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- A finite coprime intersection completes to the product of the individual completions. -/
def adicChineseRemainderEquiv :
    AdicCompletion (⨅ i, J i) R ≃ₐ[R] (∀ i, AdicCompletion (J i) R) where
  toFun x i := ⟨fun n => adicChineseQuotientEquiv J hJ n (x.val n) i, fun h => by
    rw [← adicChineseQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n => (adicChineseQuotientEquiv J hJ n).symm (fun i => (x i).val n),
    fun {m n} h => by
      apply (adicChineseQuotientEquiv J hJ m).injective
      funext i
      rw [adicChineseQuotientEquiv_transition, AlgEquiv.apply_symm_apply,
        AlgEquiv.apply_symm_apply]
      exact (x i).property h⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (adicChineseQuotientEquiv J hJ n).symm_apply_apply (x.val n)
  right_inv x := by
    funext i
    apply Subtype.ext
    funext n
    exact congrFun ((adicChineseQuotientEquiv J hJ n).apply_symm_apply (fun i => (x i).val n)) i
  map_add' x y := by
    funext i
    apply Subtype.ext
    funext n
    exact congrFun (map_add (adicChineseQuotientEquiv J hJ n) (x.val n) (y.val n)) i
  map_mul' x y := by
    funext i
    apply Subtype.ext
    funext n
    exact congrFun (map_mul (adicChineseQuotientEquiv J hJ n) (x.val n) (y.val n)) i
  commutes' r := by
    funext i
    apply Subtype.ext
    funext n
    exact congrFun ((adicChineseQuotientEquiv J hJ n).commutes r) i

end CanonicalRoots
