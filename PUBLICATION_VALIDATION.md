# Publication validation

Local checks on 2026-09-20, macOS arm64. The publication preparation adds
exposition, licensing, provenance checks, Blueprint tooling and GitHub workflows;
it does not change the existing Lean proof sources or research files.

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
