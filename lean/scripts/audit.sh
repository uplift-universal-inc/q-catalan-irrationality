#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Check all delivered project sources, excluding downloaded dependencies.
python3 scripts/check_axioms.py --scan-only

# Build the actual library before obtaining a fresh transitive axiom report.
lake build
audit_log="$(mktemp "${TMPDIR:-/tmp}/qcatalan-axioms.XXXXXXXX")"
trap 'rm -f "$audit_log"' EXIT
lake env lean QCatalan/Audit.lean | tee "$audit_log"
python3 scripts/check_axioms.py "$audit_log"
