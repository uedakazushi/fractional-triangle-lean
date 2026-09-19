import CanonicalRoots.ClassificationContract

noncomputable section
namespace CanonicalRoots

/-- Every output has a genuine isolated canonical-root realization, its canonical Ext shift,
and exactly the requested minimum number of algebra generators. -/
theorem enumerate_sound (input : Input) (e : EquationData) (he : e ∈ enumerate input) :
    EquationRealizes input e := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
  rw [← hi]
  exact classification_row_realizes input i

/-- Every independently defined actual root with an isolated minimal presentation occurs
at exactly one output position up to graded complex-algebra isomorphism. -/
theorem enumerate_complete (input : Input) (t : Target input.n input.a) :
    ∃! i : Fin (enumerate input).length,
      Nonempty (GradedAlgEquiv (rootPiece t.signature t.tau) ((enumerate input).get i).piece) :=
  t.output_complete_unique

/-- Distinct positions represent nonisomorphic graded complex algebras. -/
theorem enumerate_pairwise_nonisomorphic (input : Input)
    (i j : Fin (enumerate input).length) (hij : i ≠ j) :
    ¬Nonempty (GradedAlgEquiv ((enumerate input).get i).piece ((enumerate input).get j).piece) :=
  output_pairwise_nonisomorphic input.parameter_input i j hij

/-- The pure normal CLI payload decodes to exactly the total classifier result.
JSON text printing, the compiler/runtime, and OS output remain explicit execution boundaries. -/
theorem cli_payload_correct (input : Input) :
    decodeClassificationPayload (classificationPayload input) =
      some (input.n,input.a,enumerate input) :=
  decodeClassificationPayload_encode input.n input.a (enumerate input)

end CanonicalRoots
