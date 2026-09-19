# Manual verification

1. Build from the pinned toolchain and manifest. Run `bash scripts/verify.sh`.
   For an independent full rebuild, use an ordinary separate checkout and
   `bash scripts/acceptance.sh`; it runs `lake clean`, including dependencies.
2. Open `formal/CanonicalRoots/Final.lean`. Run `cd formal` followed by
   `lake env lean FinalSignature.lean`. Inspect all arguments, not just conclusions.
3. Follow `Target` to `Target.lean` and `Semantics.lean`. Check the genuine complex
   quotient, torsion-retaining degree group, root equation, all-point isolatedness,
   and degree-preserving `AlgEquiv`. Confirm no enumeration premise is hidden there.
4. Follow `EquationRealizes` in `ClassificationContract.lean`, and
   `HasCanonicalParameter` in `CanonicalParameter.lean`. Check that minimum generator
   count and actual Ext grading mean what the mathematical statement requires.
5. Run `lake env lean Audit.lean` and check the captured log with
   `python3 scripts/verify_all_axioms.py validation/final/axioms.log` from the root.
   The script requires an exact inventory and allows only the three standard axioms.
   `scripts/audit_sources.py formal` is an additional token scan, not a proof.
6. Inspect `OutputCertificates.lean`: these are equalities of whole equation lists,
   including order and duplicates, for ten fixed inputs. Python comparisons and
   hashes are external regressions, not extra Lean proofs.
7. Read Blueprint hypotheses against the linked source. Neither `\leanok` nor the
   declaration-existence check certifies the accuracy of natural-language prose.

The repository ships the original final logs under `evidence/original/` and a
byte-preservation manifest at `evidence/source-manifest.json`. Run
`python3 scripts/verify_sources.py` to check the preserved baseline. After an
intentional future source change, review and replace that baseline explicitly;
do not claim it still matches the old proof snapshot.

For the Japanese companion, check its pinned commit against this repository's
`git rev-parse HEAD`, then use its `scripts/check_blueprint.py --source PATH --lean`.
The companion contains no separate copy of the formalization.
