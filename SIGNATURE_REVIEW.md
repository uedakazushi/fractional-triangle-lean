# Signature review and trust boundary

This is an editorial/self-review, not independent human mathematical sign-off.
Read `formal/FinalSignature.lean` and run it with `lake env lean FinalSignature.lean`.
Expand `Target`, `RootHypersurfacePresentation`, `GradedAlgEquiv`, `RootRing`,
`EquationRealizes` and `HasCanonicalParameter` before assessing the final theorems.

The input proof fields state only `n ≥ 3` and `a ≥ 1`. `Target` is independent of
enumeration, quantifies over actual roots in the torsion-retaining quotient group,
and includes the actual isolated presentation being classified. Minimum generators
and the canonical-module shift are derived results. Completeness returns an actual
graded ring equivalence, not merely matching weights.

`#print axioms` traverses the proof dependencies. Only `propext`, `Classical.choice`
and `Quot.sound` are allowed. An allowlist pass cannot establish that a definition
captures the intended mathematical notion, nor that hypotheses are noncircular.
For `theorem_1_4`, also expand `InvertiblePolynomial`, its `IsPrincipal`
predicate, and `HigherRootRigidity`. The forward direction changes the
presentation; the converse returns the input polynomial itself with its exact
weights and degree. No atomic-type hypothesis is added to the converse.
The original detailed Japanese self-review is preserved in
`docs/archive/SIGNATURE_REVIEW.md`. The Blueprint gives a reading route and links to
exact declarations; its graph is manually curated and its prose is not kernel-checked.

The historical leanchecker replay used an imported environment and did not freshly
replay every dependency. Do not describe historical logs as a new clean build on
this publication checkout. See `PUBLICATION_VALIDATION.md` for current checks.
