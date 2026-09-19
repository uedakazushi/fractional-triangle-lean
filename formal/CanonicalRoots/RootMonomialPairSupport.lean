import CanonicalRoots.RootMonomialGeneration
import CanonicalRoots.CoprimeRootPurePowers
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section
namespace CanonicalRoots
open MvPolynomial

theorem rootMonomialBasis_point {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : ∀ i, 0 < p i)
    (τ : DegreeGroup p) (q : RootMonomialIndex p τ) (v : Fin (n + 1) → ℂ)
    (hv : ∑ i, v i ^ p i = 0) :
    rootPoint p τ (fermatPoint p v hv) (rootMonomialBasis p (hp 0) τ q) =
      ∏ i, v i ^ rootMonomialExponent p τ q i := by
  change fermatPoint p v hv (rootMonomialBasis p (hp 0) τ q : AmbientRing p) = _
  rw [rootMonomialBasis_apply, ambientMonomialBasis_apply]
  change aeval v (monomial (rootMonomialExponent p τ q) 1) = _
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp)]

theorem twoActiveCoordinates_fermat {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 0 < p i)
    (i j : Fin n) (hij : i ≠ j) (x y : ℂ) (hx : x ^ p i = 1) (hy : y ^ p j = -1) :
    ∑ k, (if k = i then x else if k = j then y else 0) ^ p k = 0 := by
  classical
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij
    (fun k _ hk => by simp [hk.1, hk.2, zero_pow (ne_of_gt (hp k))])]
  simp [Ne.symm hij, hx, hy]

/-- Every ordered coordinate pair is witnessed by a monomial generator supported
inside that pair and using its first coordinate. This follows from actual point evaluations. -/
theorem root_monomial_generators_pair_support {n a : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : AdmissibleSignature p) (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    {ι : Type*} (f : ι → RootMonomialIndex p τ)
    (hgen : Algebra.adjoin ℂ (Set.range (fun k => rootMonomialBasis p
      (lt_of_lt_of_le (by decide) (hp.1 0)) τ (f k))) = ⊤)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∃ k, rootMonomialExponent p τ (f k) i ≠ 0 ∧
      ∀ l, l ≠ i → l ≠ j → rootMonomialExponent p τ (f k) l = 0 := by
  classical
  let hp0 : ∀ l, 0 < p l := fun l => lt_of_lt_of_le (by decide) (hp.1 l)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p i)
  have hprim := Complex.isPrimitiveRoot_exp (p i) (ne_of_gt (hp0 i))
  have hζ : ζ ^ p i = 1 := hprim.pow_eq_one
  have hζu : ζ ^ canonicalRootScale p a ≠ 1 := by
    intro he
    have hd := hprim.dvd_of_pow_eq_one _ he
    have hone := Nat.eq_one_of_dvd_coprimes
      (canonicalRootScale_coprime_coordinate p hp ha τ hτ hcop i) hd (dvd_refl (p i))
    have := hp.1 i
    omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (hp0 j)
  let v : Fin (n + 1) → ℂ := fun l => if l = i then 1 else if l = j then y else 0
  let w : Fin (n + 1) → ℂ := fun l => if l = i then ζ else if l = j then y else 0
  have hv : ∑ l, v l ^ p l = 0 := twoActiveCoordinates_fermat p hp0 i j hij 1 y (one_pow _) hy
  have hw : ∑ l, w l ^ p l = 0 := twoActiveCoordinates_fermat p hp0 i j hij ζ y hζ hy
  by_contra hn
  push Not at hn
  have he : rootPoint p τ (fermatPoint p v hv) = rootPoint p τ (fermatPoint p w hw) := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro _ ⟨k, rfl⟩
    rw [rootMonomialBasis_point p hp0, rootMonomialBasis_point p hp0]
    by_cases hki : rootMonomialExponent p τ (f k) i = 0
    · apply Finset.prod_congr rfl
      intro l hl
      by_cases hli : l = i
      · subst l
        simp only [hki, pow_zero]
      · simp only [v, w, hli, ↓reduceIte]
    · obtain ⟨l, hli, hlj, hkl⟩ := hn k hki
      have hv0 : v l ^ rootMonomialExponent p τ (f k) l = 0 := by
        simp [v, hli, hlj, zero_pow hkl]
      have hw0 : w l ^ rootMonomialExponent p τ (f k) l = 0 := by
        simp [w, hli, hlj, zero_pow hkl]
      rw [Finset.prod_eq_zero (Finset.mem_univ l) hv0,
        Finset.prod_eq_zero (Finset.mem_univ l) hw0]
  have hh := AlgHom.congr_fun he (coprimeRootPurePower p hp ha τ hτ hcop i)
  rw [coprimeRootPurePower_point, coprimeRootPurePower_point, fermatPoint_X, fermatPoint_X] at hh
  have hh' : (1 : ℂ) = ζ ^ canonicalRootScale p a := by simpa only [v, w, ↓reduceIte, one_pow] using hh
  exact hζu hh'.symm

end CanonicalRoots
