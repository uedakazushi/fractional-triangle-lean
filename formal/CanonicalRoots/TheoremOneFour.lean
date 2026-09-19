import CanonicalRoots.PrincipalRootPresentation
import CanonicalRoots.TernaryInvertibleRealization
import CanonicalRoots.TernaryRootSignatureInvariant

/-!
# Manuscript Theorem 1.4

This module formalizes all clauses of Theorem 1.4 (page 4) of
`canonical_root_isolated_ja_v01.pdf`: principal invertible presentations,
the converse for arbitrary ternary invertible polynomials, signature and root
uniqueness, and the higher-dimensional criterion and rigidity.

Here `n` counts generators, `a` is the manuscript's positive `δ`, and `h`
is the relation degree. All equivalences are actual graded complex-algebra
equivalences. The original equation is not required to have determinant `h`.
-/

noncomputable section
namespace CanonicalRoots

/-- All explicit rigidity conclusions in the last paragraph of Theorem 1.4. -/
def HigherRootRigidity {n a : ℕ} (t : Target (n + 1) a) : Prop :=
  rootSubalgebra t.signature t.tau = ⊤ ∧
  (∃ H : RootHypersurfacePresentation t.signature t.tau,
    H.polynomial = fermat t.signature ∧
    H.relationDegree = ∏ i, t.signature i ∧
    (∀ i, H.weights i = (∏ j, t.signature j) / t.signature i) ∧
    Finset.univ.gcd H.weights = 1) ∧
  ∀ d : ℕ, 1 ≤ d → ∀ υ : DegreeGroup t.signature,
    IsCanonicalRoot t.signature d υ → d ∣ a ∧ d ≤ a

theorem higher_canonical_root_rigidity {n a : ℕ} (t : Target (n + 1) a)
    (hn : 3 ≤ n) : HigherRootRigidity t := by
  have hc := t.pairwise_coprime hn
  have hd := t.higher_product_defect hn
  let H := higherRootPresentation (by omega) t.signature t.admissible.1 t.parameter_input
    hc hd t.tau t.root_equation
  refine ⟨t.presentation.higher_root_eq_top t.signature t.admissible t.parameter_input
    t.tau t.root_equation hn, ⟨H,rfl,rfl,?_,?_⟩,?_⟩
  · intro i
    change productWeights t.signature i = (∏ j, t.signature j) / t.signature i
    have hp : ∀ j, 0 < t.signature j := fun j => by have := t.admissible.1 j; omega
    apply Nat.eq_div_of_mul_eq_right (ne_of_gt (hp i))
    simpa only [mul_comm] using productWeights_mul t.signature i
  · exact (show Target (n + 1) a from {t with presentation := H}).weights_gcd_eq_one
  · intro d hd υ hυ
    exact t.higher_root_index_maximal hn hd υ hυ

/-- Signature uniqueness is up to permutation (expressed as a multiset).
It applies to arbitrary graded-isomorphic ternary roots, without assuming that
their initial equations are invertible. -/
theorem ternary_signature_unique {a : ℕ} (t s : Target 3 a)
    (he : Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau)
      (rootPiece s.signature s.tau))) :
    (List.ofFn t.signature : Multiset ℕ) = (List.ofFn s.signature : Multiset ℕ) := by
  obtain ⟨e⟩ := he
  exact ternary_root_gradedEquiv_signature_eq t.signature s.signature t.admissible
    s.admissible t.parameter_input t.tau s.tau t.root_equation s.root_equation e

/-- **Theorem 1.4 of canonical_root_isolated_ja_v01, in full.**

The six conjuncts state: an invertible principal presentation for every actual
isolated root; realization of every principal ternary invertible polynomial;
uniqueness of the ternary signature up to permutation; uniqueness of the root
for each signature and positive index; the higher-dimensional arithmetic
existence criterion; and the explicit higher-dimensional rigidity conclusions.
The identity `E w = h 1` follows for each presentation from
`InvertiblePolynomial.degree_equations`.
-/
theorem theorem_1_4 :
    (∀ (n a : ℕ) (t : Target n a),
      ∃ H : RootHypersurfacePresentation t.signature t.tau,
        ∃ F : InvertiblePolynomial H.polynomial H.weights H.relationDegree,
          F.IsPrincipal ∧ H.relationDegree = a + ∑ i, H.weights i ∧
          ∀ i, ∑ j, F.exponentMatrix i j * (H.weights j : ℤ) = H.relationDegree) ∧
    (∀ (a h : ℕ) (f : MvPolynomial (Fin 3) ℂ) (w : Fin 3 → ℕ)
      (F : InvertiblePolynomial f w h),
      1 ≤ a → F.IsPrincipal → h = a + ∑ i, w i →
      ∃ t : Target 3 a, t.presentation.polynomial = f ∧
        t.presentation.weights = w ∧ t.presentation.relationDegree = h) ∧
    (∀ (a : ℕ) (t s : Target 3 a),
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau) (rootPiece s.signature s.tau)) →
      (List.ofFn t.signature : Multiset ℕ) = (List.ofFn s.signature : Multiset ℕ)) ∧
    (∀ (n a : ℕ) (p : Fin n → ℕ), (∀ i, 2 ≤ p i) → 1 ≤ a →
      ∀ τ υ : DegreeGroup p, IsCanonicalRoot p a τ → IsCanonicalRoot p a υ → τ = υ) ∧
    (∀ (n a : ℕ) (p : Fin (n + 1) → ℕ), 3 ≤ n → (∀ i, 2 ≤ p i) → 1 ≤ a →
      ((∃ t : Target (n + 1) a, t.signature = p) ↔
        Pairwise (fun i j => Nat.Coprime (p i) (p j)) ∧
          ((∏ i, p i : ℕ) : ℤ) - ∑ i, (productWeights p i : ℤ) = a)) ∧
    (∀ (n a : ℕ) (t : Target (n + 1) a), 3 ≤ n → HigherRootRigidity t) := by
  refine ⟨?_,
    fun _ _ _ _ F ha hp hd => principal_ternary_invertible_realization F ha hp hd,
    fun _ t s he => ternary_signature_unique t s he, ?_,
    fun _ _ p hn hp ha => higher_signature_target_iff p hn hp ha,
    fun _ _ t hn => higher_canonical_root_rigidity t hn⟩
  · intro n a t
    obtain ⟨H,F,hp,hd⟩ := canonical_root_invertible_presentation t
    exact ⟨H,F,hp,hd,F.degree_equations⟩
  · intro n a p hp ha τ υ hτ hυ
    exact canonicalRoot_unique p (fun i => by have := hp i; omega) ha τ υ hτ hυ

end CanonicalRoots
