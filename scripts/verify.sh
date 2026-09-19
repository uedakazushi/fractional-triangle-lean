#!/usr/bin/env bash
# Incremental publication verification. acceptance.sh is the separate full-clean gate.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
mkdir -p validation/final validation/publication
python3 scripts/verify_sources.py
python3 scripts/audit_sources.py formal
cd formal
lake build
lake build canonical_roots
lake env lean CanonicalRoots/Final.lean
lake env lean Audit.lean > ../validation/final/axioms.log
lake env lean Tests.lean
lake env lean FinalSignature.lean > ../validation/publication/final-signatures.log
cd ..
python3 scripts/verify_all_axioms.py validation/final/axioms.log
python3 scripts/test_final_cli.py
python3 scripts/test_final_boundaries.py
python3 scripts/check_blueprint.py --lean
