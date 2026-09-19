import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Finiteness.Ideal

noncomputable section
namespace CanonicalRoots
variable {R : Type*} [CommRing R]

def adicRefinementQuotient (I J : Ideal R) (φ : ℕ → ℕ)
    (h : ∀ n : ℕ, I ^ φ n ≤ J ^ n) (n : ℕ) :
    (R ⧸ (I ^ φ n • ⊤ : Ideal R)) →ₐ[R] (R ⧸ (J ^ n • ⊤ : Ideal R)) :=
  Ideal.Quotient.factorₐ R (by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h n)

theorem adicRefinementQuotient_transition (I J : Ideal R) (φ : ℕ → ℕ)
    (hφ : Monotone φ) (h : ∀ n : ℕ, I ^ φ n ≤ J ^ n) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap J R hmn (adicRefinementQuotient I J φ h n (x.val (φ n))) =
      adicRefinementQuotient I J φ h m (x.val (φ m)) := by
  rw [← x.property (hφ hmn)]
  generalize x.val (φ n) = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- The actual map of completions induced by a monotone refinement of ideal powers. -/
def adicRefinement (I J : Ideal R) (φ : ℕ → ℕ) (hφ : Monotone φ)
    (h : ∀ n : ℕ, I ^ φ n ≤ J ^ n) : AdicCompletion I R →ₐ[R] AdicCompletion J R where
  toFun x := ⟨fun n => adicRefinementQuotient I J φ h n (x.val (φ n)),
    adicRefinementQuotient_transition I J φ hφ h x⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (adicRefinementQuotient I J φ h n) (x.val (φ n)) (y.val (φ n))
  map_mul' x y := by
    apply Subtype.ext
    funext n
    exact map_mul (adicRefinementQuotient I J φ h n) (x.val (φ n)) (y.val (φ n))
  commutes' r := by apply Subtype.ext; funext n; exact (adicRefinementQuotient I J φ h n).commutes r

@[simp] theorem adicRefinement_val (I J : Ideal R) (φ : ℕ → ℕ) (hφ : Monotone φ)
    (h : ∀ n : ℕ, I ^ φ n ≤ J ^ n) (x : AdicCompletion I R) (n : ℕ) :
    (adicRefinement I J φ hφ h x).val n = adicRefinementQuotient I J φ h n (x.val (φ n)) := rfl

/-- Refining the same ideal gives the original completed element. -/
theorem adicRefinement_self (I : Ideal R) (φ : ℕ → ℕ) (hφ : Monotone φ)
    (hφid : ∀ n, n ≤ φ n) (h : ∀ n : ℕ, I ^ φ n ≤ I ^ n) :
    adicRefinement I I φ hφ h = AlgHom.id R _ := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  funext n
  change adicRefinementQuotient I I φ h n (x.val (φ n)) = x.val n
  rw [← x.property (hφid n)]
  generalize x.val (φ n) = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

theorem adicRefinement_comp (I J K : Ideal R) (φ ψ : ℕ → ℕ)
    (hφ : Monotone φ) (hψ : Monotone ψ)
    (hIJ : ∀ n : ℕ, I ^ φ n ≤ J ^ n) (hJK : ∀ n : ℕ, J ^ ψ n ≤ K ^ n) :
    (adicRefinement J K ψ hψ hJK).comp (adicRefinement I J φ hφ hIJ) =
      adicRefinement I K (φ ∘ ψ) (hφ.comp hψ) (fun n => (hIJ (ψ n)).trans (hJK n)) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  funext n
  change adicRefinementQuotient J K ψ hJK n
    (adicRefinementQuotient I J φ hIJ (ψ n) (x.val (φ (ψ n)))) =
      adicRefinementQuotient I K (φ ∘ ψ) _ n (x.val (φ (ψ n)))
  generalize x.val (φ (ψ n)) = y
  induction y using Submodule.Quotient.induction_on with | _ y => rfl

/-- Comparable ideals whose powers contain one another have the same actual completion. -/
def adicCofinalEquiv (I J : Ideal R) (hIJ : I ≤ J) (k : ℕ) (hk : 1 ≤ k) (hJI : J ^ k ≤ I) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion J R := by
  have hf (n : ℕ) : I ^ n ≤ J ^ n := pow_le_pow_left' hIJ n
  have hg (n : ℕ) : J ^ (k * n) ≤ I ^ n := by
    rw [pow_mul]
    exact pow_le_pow_left' hJI n
  have hm : Monotone (fun n : ℕ => k * n) := fun _ _ h => Nat.mul_le_mul_left k h
  have hid (n : ℕ) : n ≤ k * n := by simpa using Nat.mul_le_mul_right n hk
  apply AlgEquiv.ofAlgHom (adicRefinement I J id monotone_id hf)
    (adicRefinement J I (fun n => k * n) hm hg)
  · rw [adicRefinement_comp]
    exact adicRefinement_self J _ _ hid _
  · rw [adicRefinement_comp]
    exact adicRefinement_self I _ _ hid _

/-- Passing to a finitely generated radical does not change the adic completion. -/
def adicRadicalEquiv (I : Ideal R) (hfg : I.radical.FG) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion I.radical R := by
  let k := (I.exists_radical_pow_le_of_fg hfg).choose
  have hk : I.radical ^ k ≤ I := (I.exists_radical_pow_le_of_fg hfg).choose_spec
  exact adicCofinalEquiv I I.radical Ideal.le_radical (k + 1) (Nat.le_add_left 1 k)
    ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)

end CanonicalRoots
