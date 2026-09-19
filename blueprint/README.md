# Lean Blueprint

This is a real Lean Blueprint project: `src/web.tex` loads the upstream `blueprint`
package, and `content.tex` uses `\lean`, `\leanok` and `\uses`.

The wrapper uses `plastex` directly, which upstream supports, so the original
`formal/` Lake layout and dependency lock remain unchanged. There is no fake
Blueprint graph renderer. Our additional source browser makes the generated Lean
links usable without requiring a second doc-gen Lean dependency tree.

`python3 scripts/check_blueprint.py --lean` checks names and allowed axioms in the
compiled Lean environment. This replaces the optional upstream `checkdecls` helper;
it does not claim that `leanblueprint checkdecls` is configured at repository root.
Use the repository build commands in the README rather than `leanblueprint new`.

The 34-node map is a curated overview with proof sketches, not exhaustive theorem
coverage or automated validation of the natural-language statements. Both editions
share the exact same declaration and edge manifest.
