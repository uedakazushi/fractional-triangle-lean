import CanonicalRoots.HigherEquationArity
import CanonicalRoots.HigherSignatureList

noncomputable section
namespace CanonicalRoots

theorem higherEquation_relationDegree (a : ℕ) (ps : List ℕ) :
    (higherEquation a ps).relationDegree = ((∏ i, ps.get i : ℕ) : ℤ) := by
  rw [← intProduct_ofFn ps.get, List.ofFn_get]
  rfl

theorem higherEquation_realization {a : ℕ} (ha : 1 ≤ a) (ps : List ℕ)
    (hlen : 3 ≤ ps.length) (hp : ∀ i, 2 ≤ ps.get i)
    (hc : Pairwise (fun i j => Nat.Coprime (ps.get i) (ps.get j)))
    (hd : ((∏ i, ps.get i : ℕ) : ℤ) - ∑ i, (productWeights ps.get i : ℤ) = a) :
    ∃ t : Target ps.length a, List.ofFn t.signature = ps ∧
      t.presentation.weights = (higherEquation a ps).natWeights ∧
      (t.presentation.relationDegree : ℤ) = (higherEquation a ps).relationDegree ∧
      t.presentation.polynomial = (higherEquation a ps).polynomial := by
  have hp0 : ∀ i, 0 < ps.get i := fun i => lt_of_lt_of_le (by decide) (hp i)
  obtain ⟨τ,hτ,_⟩ := higher_root_exists_unique ps.get hp0 (by omega) hc hd
  let H := (higherRootPresentation (by omega) ps.get hp (by omega) hc hd τ hτ).renameGenerators
    (displayVariablePermutation (higherCoordinateWeight ps.get)).symm
  let t : Target ps.length a := ⟨hlen,ha,ps.get,product_defect_admissible ps.get hp (by omega) hd,τ,hτ,H⟩
  refine ⟨t,List.ofFn_get ps,?_,?_,?_⟩
  · change productWeights ps.get ∘ displayVariablePermutation (higherCoordinateWeight ps.get) = _
    exact (higherEquation_natWeights a ps hp0).symm
  · change ((∏ i, ps.get i : ℕ) : ℤ) = _
    exact (higherEquation_relationDegree a ps).symm
  · change MvPolynomial.rename (displayVariablePermutation (higherCoordinateWeight ps.get)).symm (fermat ps.get) = _
    exact (higherEquation_polynomial a ps).symm

theorem higherEquation_realization_of_mem {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a) (ps : List ℕ)
    (hm : ps ∈ enumerateHigherCandidates n a) :
    ∃ t : Target ps.length a, List.ofFn t.signature = ps ∧
      t.presentation.weights = (higherEquation a ps).natWeights ∧
      (t.presentation.relationDegree : ℤ) = (higherEquation a ps).relationDegree ∧
      t.presentation.polynomial = (higherEquation a ps).polynomial := by
  have hA := (enumerateHigherCandidates_iff n a ha ps).mp hm
  have hp : ∀ i, 2 ≤ ps.get i := fun i => hA.2.1 _ (List.get_mem _ i)
  have hm' : List.ofFn ps.get ∈ enumerateHigherCandidates ps.length a := by
    rw [List.ofFn_get, hA.1]
    exact hm
  obtain ⟨_,_,hc,hd⟩ := (enumerateHigherCandidates_ofFn_iff ps.get
    (fun i => lt_of_lt_of_le (by decide) (hp i)) ha).mp hm'
  exact higherEquation_realization ha ps (by rw [hA.1]; exact hn) hp hc hd

end CanonicalRoots
