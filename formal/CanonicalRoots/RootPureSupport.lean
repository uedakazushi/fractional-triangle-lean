import CanonicalRoots.RootMonomialPairSupport
import CanonicalRoots.PairSupportCounting

noncomputable section
namespace CanonicalRoots
open MvPolynomial

variable {n a : ℕ} (p : Fin (n + 1) → ℕ) (hp : AdmissibleSignature p)
  (ha : 1 ≤ a) (τ : DegreeGroup p) (hτ : IsCanonicalRoot p a τ)
  (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))

theorem rootMonomial_singleton_mem_pure_adjoin (q : RootMonomialIndex p τ) (i : Fin (n + 1))
    (hs : (rootMonomialExponent p τ q).support = {i}) :
    rootMonomialBasis p (lt_of_lt_of_le (by decide) (hp.1 0)) τ q ∈
      Algebra.adjoin ℂ (Set.range (coprimeRootPurePower p hp ha τ hτ hcop)) := by
  classical
  let d := rootMonomialExponent p τ q
  have hd : d = Finsupp.single i (d i) := by
    ext l
    by_cases hli : l = i
    · subst l; simp
    · have he : d l = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rw [show d.support = {i} from hs]
        simpa only [Finset.mem_singleton] using hli
      simp [he, Ne.symm hli]
  have hdr : ∃ m : ℕ, d i • xDegree p i = m • τ := by
    obtain ⟨m, hm⟩ := q.property
    change Finsupp.weight (xDegree p) d = m • τ at hm
    rw [hd, Finsupp.weight_single] at hm
    exact ⟨m, hm⟩
  obtain ⟨k, hk⟩ := (pure_power_root_degree_iff p hp ha τ hτ hcop i (d i)).mp hdr
  have he : rootMonomialBasis p (lt_of_lt_of_le (by decide) (hp.1 0)) τ q =
      coprimeRootPurePower p hp ha τ hτ hcop i ^ k := by
    apply Subtype.ext
    rw [rootMonomialBasis_apply, ambientMonomialBasis_apply]
    change ambientQuotient p (monomial d 1) =
      (ambientQuotient p (X i ^ canonicalRootScale p a)) ^ k
    rw [hd, ← X_pow_eq_monomial, hk, pow_mul, map_pow]
  rw [he]
  exact (Algebra.adjoin ℂ (Set.range (coprimeRootPurePower p hp ha τ hτ hcop))).pow_mem
    (Algebra.subset_adjoin ⟨i, rfl⟩) k

/-- The actual hypersurface generator count and the ordered-pair test force all
selected monomials into the pure-power subalgebra. -/
theorem RootHypersurfacePresentation.pure_power_generation
    (H : RootHypersurfacePresentation p τ) (hn : 3 ≤ n) :
    Algebra.adjoin ℂ (Set.range (coprimeRootPurePower p hp ha τ hτ hcop)) = ⊤ := by
  classical
  let hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le (by decide) (hp.1 i)
  obtain ⟨f, _, hgen, _⟩ := H.exists_monomial_generators p hp0 τ hp ha hτ
  let S : Fin (n + 1) → Finset (Fin (n + 1)) := fun k =>
    (rootMonomialExponent p τ (f k).val).support
  have hcover : ∀ i j : Fin (n + 1), i ≠ j → ∃ k, i ∈ S k ∧ S k ⊆ {i, j} := by
    intro i j hij
    obtain ⟨k, hi, hother⟩ := root_monomial_generators_pair_support p hp ha τ hτ hcop
      (fun k => (f k).val) hgen i j hij
    refine ⟨k, Finsupp.mem_support_iff.mpr hi, ?_⟩
    intro l hl
    by_cases hli : l = i
    · simp [hli]
    by_cases hlj : l = j
    · simp [hlj]
    exact False.elim ((Finsupp.mem_support_iff.mp hl) (hother l hli hlj))
  have hsingle := singleton_supports_of_pair_cover S
    (by simp only [Fintype.card_fin]; omega) (le_refl _) hcover
  choose g hg using hsingle
  have hginj : Function.Injective g := by
    intro i j hij
    apply Finset.singleton_injective
    rw [← hg i, ← hg j, hij]
  have hgsurj := Finite.surjective_of_injective hginj
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, hi⟩ := hgsurj k
  exact rootMonomial_singleton_mem_pure_adjoin p hp ha τ hτ hcop (f k).val i
    (by change S k = {i}; rw [← hi, hg])

end CanonicalRoots
