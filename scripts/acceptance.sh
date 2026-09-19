#!/usr/bin/env bash
# Run ONLY after the agent has implemented the actual final project.
# This gate deliberately fails on the initial smoke-test scaffold.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
for required in formal/CanonicalRoots/Final.lean formal/Audit.lean formal/Tests.lean formal/Main.lean SPEC_CONTRACT.md SIGNATURE_REVIEW.md; do
  if [ ! -f "$ROOT/$required" ]; then
    printf 'INCOMPLETE: missing %s\n' "$required" >&2
    exit 2
  fi
done
command -v lake >/dev/null 2>&1 || { printf 'Lake is not installed.\n' >&2; exit 2; }
LOGDIR="$ROOT/validation/final"
mkdir -p "$LOGDIR"
python3 "$ROOT/scripts/audit_sources.py" "$ROOT/formal" | tee "$LOGDIR/source_scan.log"
cd "$ROOT/formal"
lake clean 2>&1 | tee "$LOGDIR/clean.log"
lake build 2>&1 | tee "$LOGDIR/build.log"
lake build canonical_roots 2>&1 | tee "$LOGDIR/executable_build.log"
lake env lean CanonicalRoots/Final.lean 2>&1 | tee "$LOGDIR/final_module.log"
lake env lean Audit.lean 2>&1 | tee "$LOGDIR/axioms.log"
python3 "$ROOT/scripts/check_axioms_log.py" "$LOGDIR/axioms.log" | tee "$LOGDIR/axiom_allowlist.log"
lake env lean Tests.lean 2>&1 | tee "$LOGDIR/tests.log"
lake exe canonical_roots 3 1 > "$LOGDIR/n3_a1.json"
lake exe canonical_roots 3 6 > "$LOGDIR/n3_a6.json"
lake exe canonical_roots 4 1 > "$LOGDIR/n4_a1.json"
python3 "$ROOT/scripts/validate_outputs.py" "$LOGDIR" | tee "$LOGDIR/output_regression.log"
printf 'Build/audit commands completed. Read SPEC_CONTRACT.md and SIGNATURE_REVIEW.md; do not infer semantic correctness merely from this exit code.\n'
