# Publication validation

## Theorem 1.4 extension (2026-09-20)

The repository now includes `CanonicalRoots.theorem_1_4`, covering every clause
of the requested manuscript theorem. Six new mathematical modules prove the
missing arbitrary-polynomial converse and package the existing classification
results. The aggregate import, audit and signature display were extended.
The public repository metadata uses `uedakazushi/fractional-triangle-lean`;
the Blueprint title is *Isolated hypersurface fractional triangle singularities*.

- `bash scripts/verify.sh` passed: library and executable build, final signatures,
  existing Lean tests, CLI regressions, source scan, and Blueprint checks.
- All 1,633 requested axiom reports passed the allowlist. In particular,
  `theorem_1_4` uses only `propext`, `Classical.choice`, and `Quot.sound`.
  The 32 added reports are saved in `evidence/theorem-1.4-axioms.log`.
- The CLI tests still pass on 35 legal inputs / 528 equation records and seven
  invalid inputs; the preserved boundary-data comparisons also pass.
- All 400 current source-manifest entries match. The 19 original research and
  reference files are unchanged. The original 394-file manifest remains archived.
- The Blueprint now has 34 nodes and 56 exact Lean references, all resolved and
  axiom-checked. English HTML/PDF generation and the site check passed:
  41 HTML files, 3,239 local links, 112 Lean links.
- The updated seven-page English PDF was rendered and inspected, including its
  title and the full new manuscript-theorem section.

These are incremental checks using the pinned installed dependencies. A new
full-clean dependency rebuild was not performed for this extension. The
historical acceptance run below remains a record of the original source snapshot.
The theorem's clause correspondence and input definitions are documented in
`docs/THEOREM_1_4.md` and exposed by `formal/FinalSignature.lean`.

## Initial publication preparation

Earlier local checks on 2026-09-20, macOS arm64. The initial publication preparation added
exposition, licensing, provenance checks, Blueprint tooling and GitHub workflows;
at that stage it did not change the existing Lean proof sources or research files.

- 394 baseline files in formal/, research/ and reference/ matched their original bytes.
- The pinned Lean project and executable built successfully in the new checkout.
- Final.lean, Tests.lean and FinalSignature.lean were checked again.
- All 1,601 declarations requested by Audit.lean used only the allowed foundational
  axioms: propext, Classical.choice and Quot.sound.
- The CLI regressions passed for 35 legal inputs and 528 equation records, plus
  seven invalid-input cases and the preserved boundary-data comparisons.
- The English Blueprint has 27 nodes and 43 Lean declaration references. The
  curated graph is acyclic. Every reference resolved in Lean and passed the same
  axiom allowlist.
- Lean Blueprint 0.0.20 with plasTeX 3.1 generated HTML and a LuaLaTeX PDF.
  The generated local links and declaration-source links were checked.

This publication run reused the installed pinned dependency cache and cloned local
build artifacts. It is an incremental validation, not a new full clean build.
The prior full-clean acceptance gate (2026-09-19, 4,243 seconds) is recorded under
`evidence/original/`, with normalized machine paths. The local cache was subsequently made independent with filesystem copies, so
cleaning this checkout will not affect the original workspace. An ordinary fresh
clone also has its own dependencies and can run the full acceptance script or
the optional full-clean GitHub workflow.

The GitHub workflow files have been prepared and inspected, but have not been run
on GitHub. No repository was pushed and no Pages deployment was performed.
Natural-language Blueprint correspondence and theorem meaning still require human
review; no independent mathematical sign-off is claimed.

The five-page English PDF was rendered to images and visually inspected.
The HTML navigation and mathematical rendering were also inspected in a browser.
The original CSV uses CRLF and some historical logs have trailing spaces; these
are retained deliberately, with Git attributes preserving the baseline bytes.
GitHub workflow YAML and action expressions passed actionlint 1.7.7; citation
metadata and all three author entries were parsed successfully. Actual hosted CI
execution remains pending publication.
