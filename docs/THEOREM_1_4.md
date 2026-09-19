# The Invertibility and Rigidity Theorem

The formal declaration is `CanonicalRoots.theorem_1_4` in
[`TheoremOneFour.lean`](../formal/CanonicalRoots/TheoremOneFour.lean).
It is exported by `import CanonicalRoots`.

The requested source is page 4 of `canonical_root_isolated_ja_v01.pdf`,
SHA-256 `2398e5207de3342fef3ab8986e0d3cb3ce173e2d5e22edc65a0d69c6f0a8d9d1`.
The corresponding statement is also Theorem 1.4, labelled `thm:main`, in the
preserved [v02 manuscript](../research/current/canonical_root_isolated_ja_v02.tex).
No research file was edited.

Lean's `n` counts variables/minimal generators, so the ring dimension is `n-1`.
Lean's positive parameter `a` is the manuscript's `δ`. The higher-dimensional
clauses use `Fin (n+1)` and `3 ≤ n`, hence at least four variables.

| Manuscript clause | Lean conclusion |
| --- | --- |
| An invertible presentation exists in every dimension | A new `RootHypersurfacePresentation` of the same actual root ring, an `InvertiblePolynomial` witness, primitive weights, absolute determinant equal to `h`, `h = a + Σwᵢ`, and explicit `Ew = h1`. |
| Every principal ternary invertible polynomial is realized | A `Target 3 a` whose presentation polynomial, weights, and relation degree equal the input exactly. Coefficients can be any nonzero complex numbers. |
| The ternary signature is unique up to order | Graded-isomorphic roots at the same positive index have equal signature multisets. |
| The root is unique | Two roots of the same canonical element at the same positive index in the same degree group are equal. |
| Higher-dimensional existence criterion | An actual target with the given signature exists iff its entries are pairwise coprime and its product defect equals `a`. |
| Higher-dimensional rigidity | The actual root subalgebra equals the ambient algebra; a primitive Fermat presentation has degree `Πpᵢ` and weights `Πpⱼ/pᵢ`; every other positive root index divides `a` and is at most `a`. |

The forward assertion does not require the equation initially supplied with the
target to have determinant `h`. It proves the existence of a suitable equation.
The converse does not assume that the input is one of the five Cox types:
`InvertiblePolynomial` has only polynomial, matrix, weight and isolatedness
conditions. Three distinct axis monomials exhaust its three-term support;
branched types would force a fourth term. Permutations then identify the exponent
matrix with a Cox matrix. The determinant condition fixes the weight scaling.

The coefficient-normalization argument uses mathlib's complex logarithm,
exponential, and matrix invertibility: solve `Ev = log(c)` and exponentiate.
The induced diagonal substitutions and the variable permutation are transported
to actual graded quotient-algebra equivalences before applying the existing Cox
realization theorem.

The six new modules are `InvertiblePolynomial`, `DiagonalPolynomialEquiv`,
`TernaryInvertibleSupport`, `TernaryInvertibleRealization`,
`PrincipalRootPresentation`, and `TheoremOneFour`. The existing mathematical
modules and `Final.lean` were not changed. The aggregate import, axiom audit,
and displayed-signature file were extended.

The original 394-file manifest is retained at
`evidence/original/source-manifest.json`. The current 400-file manifest includes
the six added modules and the three deliberately updated Lean entry/audit files.
The research and reference hashes remain identical to the original snapshot.
Run `bash scripts/verify.sh` for the current incremental build, axiom audit,
signature checks, regression suite, and Blueprint declaration checks.
