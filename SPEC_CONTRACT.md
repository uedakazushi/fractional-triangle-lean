# Semantic contract

Inputs are `n ≥ 3`, `a ≥ 1`. The degree group is the actual quotient
`L = (ℤⁿ ⊕ ℤc)/⟨pᵢxᵢ − c⟩`, including torsion, for `pᵢ ≥ 2` and `Σ 1/pᵢ < 1`.
The actual ambient quotient is `T = ℂ[X]/(Σ Xᵢ^pᵢ)`. A canonical root is an actual
`τ ∈ L` with `aτ = c − Σxᵢ`; the root subalgebra is `R = ⊕ₘ≥₀ Tₘτ`.
`Semantics.lean` and `Target.lean` define this domain without importing enumeration.

`Target` quantifies over every such signature and root with an actual isolated
homogeneous hypersurface presentation: positive weights, nonzero homogeneous
polynomial, no constant or linear terms, gradient zero only at the origin for all
complex points, and a degree-preserving algebra equivalence to R. Minimality is
proved against every alternative surjective polynomial presentation. The canonical
parameter is connected to the actual Ext¹ module and all integer graded pieces.

| Public declaration | Exact role |
| --- | --- |
| `enumerate_sound` | Every output row satisfies `EquationRealizes`: matching dimension and parameter, sorted positive primitive weights, nonnegative exponent data, an actual target with matching equation, signature and root witness, the canonical Ext shift and minimum number of algebra generators. |
| `enumerate_complete` | Every independently defined `Target input.n input.a` is graded-isomorphic to the equation at exactly one output position. |
| `enumerate_pairwise_nonisomorphic` | Distinct output positions admit no graded complex-algebra equivalence. |
| `cli_payload_correct` | The pure payload decoder returns exactly `some (n, a, enumerate input)`. |

The actual Lean types are authoritative. No classification bridge, normal-form
existence, Cox lift or fixed-ring identification is an unproved public hypothesis.
The predicate `EquationRealizes` does not define its domain through list membership.

JSON text parsing/printing, runtime execution, OS output and external hashes are
outside the pure payload theorem. The decoder restores the EquationData fields;
redundant display fields are not a byte-authentication contract. Concrete whole-list
certificates are separate from ordinary compiled execution. Human comparison of
these definitions with the intended mathematics remains essential.
