import CanonicalRoots.InvertiblePolynomial
import CanonicalRoots.CoxCandidateRelation
import CanonicalRoots.CoxWeightNormalization

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem axisSupportExponent_main {n : ℕ} (i j : Fin n) (k : ℕ) :
    axisSupportExponent i j k i = k := by
  by_cases hij : i = j
  · simp [axisSupportExponent, hij]
  · simp [axisSupportExponent, hij]

theorem axisSupportExponent_other_le_one {n : ℕ} (i j l : Fin n) (k : ℕ)
    (hli : l ≠ i) : axisSupportExponent i j k l ≤ 1 := by
  by_cases hij : i = j
  · subst j
    simp [axisSupportExponent, Ne.symm hli]
  · simp only [axisSupportExponent, ite_eq_right hij, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega

theorem axisSupportExponent_injective {n : ℕ} (s : Fin n → Fin n)
    (k : Fin n → ℕ) (hk : ∀ i, 2 ≤ k i) :
    Function.Injective (fun i => axisSupportExponent i (s i) (k i)) := by
  intro i j he
  by_contra hij
  have hmain := axisSupportExponent_main i (s i) (k i)
  have hother := axisSupportExponent_other_le_one j (s j) i (k j) hij
  have hh := congrArg (fun d : Fin n →₀ ℕ => d i) he
  dsimp only at hh
  have := hk i
  omega

/-- An invertible ternary polynomial with positive defect has precisely one of
the five unbranched supports, up to permutations of terms and variables.
The two branched possibilities would require a fourth nonzero monomial. -/
theorem InvertiblePolynomial.ternary_support {h : ℕ} {f : MvPolynomial (Fin 3) ℂ}
    {w : Fin 3 → ℕ} (F : InvertiblePolynomial f w h) (hdef : (∑ i, w i) < h) :
    ∃ σ ρ : Equiv.Perm (Fin 3), ∃ tag : Fin 5, ∃ k : Fin 3 → ℕ,
      (∀ i, 2 ≤ k i) ∧ ∀ i,
        F.exponent (ρ i) =
          axisSupportExponent (σ i) (σ (threeAxisPattern ⟨tag.val, by omega⟩ i)) (k i) := by
  classical
  obtain ⟨σ,tag,k,hk,hc,ht⟩ := isolated_ternary_five_or_branched_link f F.isolated
    F.no_constant_or_linear w F.weights_pos F.homogeneous hdef
  choose r hr using fun i => F.exists_exponent_of_coeff_ne_zero _ (hc i)
  have hinj : Function.Injective r := by
    intro i j hij
    have he := (hr i).symm.trans ((congrArg F.exponent hij).trans (hr j))
    by_contra hne
    have hmain := axisSupportExponent_main (σ i) (σ (threeAxisPattern tag i)) (k i)
    have hother := axisSupportExponent_other_le_one (σ j) (σ (threeAxisPattern tag j))
      (σ i) (k j) (σ.injective.ne hne)
    have hh := congrArg (fun d : Fin 3 →₀ ℕ => d (σ i)) he
    have := hk i
    omega
  let ρ : Equiv.Perm (Fin 3) := Equiv.ofBijective r
    ((Finite.injective_iff_bijective).mp hinj)
  have htag : tag.val < 5 := by
    rcases ht with ht | ⟨m,l,hm,hl,hcoeff⟩
    · exact ht
    by_contra ht
    have hcases : tag = 5 ∨ tag = 6 := by
      have : tag.val = 5 ∨ tag.val = 6 := by omega
      rcases this with he | he
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext he)
    obtain ⟨j,hj⟩ := F.exists_exponent_of_coeff_ne_zero _ hcoeff
    obtain ⟨i,rfl⟩ := ρ.surjective j
    have he := (hr i).symm.trans hj
    have he1 := congrArg (fun d : Fin 3 →₀ ℕ => d (σ 1)) he
    rcases hcases with rfl | rfl <;> fin_cases i <;>
      simp [axisSupportExponent, threeAxisPattern, σ.injective.eq_iff] at he1
    all_goals have := hk 1; omega
  exact ⟨σ,ρ,⟨tag.val,htag⟩,k,hk,hr⟩

theorem axisKind_exponent (tag : Fin 5) (k : Fin 3 → ℕ) (i j : Fin 3) :
    (axisSupportExponent i (threeAxisPattern ⟨tag.val, by omega⟩ i) (k i) j : ℤ) =
      Cox.exponents (axisKind tag) (k 0) (k 1) (k 2) i j := by
  fin_cases tag <;> fin_cases i <;> fin_cases j <;>
    simp [axisSupportExponent, threeAxisPattern, axisKind, Cox.exponents]

/-- The five-support reduction relates the input matrix to the Cox matrix by
actual row and column permutations, hence preserves its absolute determinant. -/
theorem InvertiblePolynomial.ternary_cox_matrix {h : ℕ}
    {f : MvPolynomial (Fin 3) ℂ} {w : Fin 3 → ℕ}
    (F : InvertiblePolynomial f w h) (hdef : (∑ i, w i) < h) :
    ∃ σ ρ : Equiv.Perm (Fin 3), ∃ e : TernaryCandidate,
      2 ≤ e.alpha ∧ 2 ≤ e.beta ∧ 2 ≤ e.gamma ∧
      (∀ i j, (F.exponent (ρ i) (σ j) : ℤ) =
        Cox.exponents e.kind e.alpha e.beta e.gamma i j) := by
  obtain ⟨σ,ρ,tag,k,hk,he⟩ := F.ternary_support hdef
  refine ⟨σ,ρ,⟨axisKind tag,k 0,k 1,k 2⟩,hk 0,hk 1,hk 2,?_⟩
  intro i j
  rw [he i]
  have ha : axisSupportExponent (σ i) (σ (threeAxisPattern ⟨tag.val, by omega⟩ i))
      (k i) (σ j) = axisSupportExponent i (threeAxisPattern ⟨tag.val, by omega⟩ i) (k i) j := by
    by_cases hi : i = threeAxisPattern ⟨tag.val, by omega⟩ i
    · rw [axisSupportExponent, ite_eq_left (congrArg σ hi), axisSupportExponent, ite_eq_left hi]
      simp only [Finsupp.single_apply, σ.injective.eq_iff]
    · rw [axisSupportExponent, ite_eq_right (σ.injective.ne hi), axisSupportExponent, ite_eq_right hi]
      simp only [Finsupp.add_apply, Finsupp.single_apply, σ.injective.eq_iff]
  rw [ha]
  exact axisKind_exponent tag k i j

end CanonicalRoots
