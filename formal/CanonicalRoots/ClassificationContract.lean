import CanonicalRoots.ClassificationPayloadCodec
import CanonicalRoots.OutputWellFormed
import CanonicalRoots.CanonicalParameter

noncomputable section
namespace CanonicalRoots

/-- The public semantic contract of an equation, independent of membership in the enumeration.
The witness is an actual torsion-retaining canonical root and an actual isolated graded presentation.
The contract additionally includes the canonical Ext shift and the least possible generator count. -/
def EquationRealizes (input : Input) (e : EquationData) : Prop :=
  e.n = input.n ∧ e.a = input.a ∧
  e.weights.length = input.n ∧ e.weights.SortedLE ∧ (∀ w ∈ e.weights, 0 < w) ∧
  Finset.univ.gcd e.natWeights = 1 ∧
  e.exponents.length = input.n ∧
  (∀ row ∈ e.exponents, row.length = input.n ∧ ∀ x ∈ row, 0 ≤ x) ∧
  ∃ t : Target e.n input.a,
    t.presentation.polynomial = e.polynomial ∧ t.presentation.weights = e.natWeights ∧
    (t.presentation.relationDegree : ℤ) = e.relationDegree ∧
    e.orderedSignature = List.ofFn (fun j => (t.signature j : ℤ)) ∧
    rootWitnessDegree input.a t.signature = t.tau ∧
    HasCanonicalParameter t.presentation.polynomial t.presentation.polynomial_ne_zero
      t.presentation.weights t.presentation.relationDegree input.a ∧
    (∃ q : MvPolynomial (Fin input.n) ℂ →ₐ[ℂ] RootRing t.signature t.tau, Function.Surjective q) ∧
    (∀ m : ℕ, ∀ q : MvPolynomial (Fin m) ℂ →ₐ[ℂ] RootRing t.signature t.tau,
      Function.Surjective q → input.n ≤ m)

theorem classification_row_realizes (input : Input) (i : Fin (enumerate input).length) :
    EquationRealizes input ((enumerate input).get i) := by
  have hn := input.dimension_input
  have ha := input.parameter_input
  obtain ⟨t,hf,hw,hd,hp,hτ⟩ := output_root_witness hn ha i
  have hn' := (output_dimensions ha i).1
  refine ⟨hn',(output_dimensions ha i).2,output_weights_length ha i,
    output_weights_sorted i,output_weights_positive hn ha i,output_weights_primitive hn ha i,
    output_exponents_length ha i,output_exponents_nonnegative ha i,
    t,hf,hw,hd,hp,hτ,t.canonical_parameter,?_,?_⟩
  · obtain ⟨q,hq⟩ := t.presentation.exists_minimal_surjection
    refine ⟨q.comp (MvPolynomial.renameEquiv ℂ (finCongr hn')).symm.toAlgHom,?_⟩
    exact hq.comp (MvPolynomial.renameEquiv ℂ (finCongr hn')).symm.surjective
  · intro m q hq
    exact hn' ▸ t.presentation.root_minimum_generators q hq

end CanonicalRoots
