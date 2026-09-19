# Contributing

Keep the mathematical domain independent of enumeration. Do not add unproved
classification assumptions, custom axioms, `sorry`, `admit` or native evaluation
into the proof closure. Preserve `research/` byte for byte; document corrections
separately. Run `bash scripts/verify.sh` for proof changes. Read the expanded final
theorem types as well as the axiom reports.

Blueprint text must point to existing declarations with accurate hypotheses.
Update nodes.json, prose and dependency edges together. Run the declaration check,
HTML/PDF build and link check. The graph is a curated outline, not an exact
extraction of Lean proof dependencies. Do not equate a green node with human review.
