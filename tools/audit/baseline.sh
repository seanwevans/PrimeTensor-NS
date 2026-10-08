#!/usr/bin/env bash
# Rebuild project outputs and retain build/contract evidence under .lake/audit.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
mode="${1:---fresh}"
case "$mode" in
  --fresh|--reuse-build) ;;
  *) printf 'Usage: bash tools/audit/baseline.sh [--fresh|--reuse-build]\n' >&2; exit 2 ;;
esac
report="$PWD/.lake/audit/$(date -u +%Y%m%dT%H%M%SZ)-$$"
mkdir -p "$report"
finish() {
  local status=$?
  printf '%s\n' "$status" > "$report/exit-code.txt"
  if (( status == 0 )); then
    printf 'PASS: supported root build and selected contract checks. Known source gaps remain.\n' > "$report/result.txt"
  else
    printf 'FAIL: baseline incomplete (exit %s).\n' "$status" > "$report/result.txt"
  fi
  printf 'Baseline evidence: %s\n' "$report"
}
trap finish EXIT
printf '%s\n' "$mode" > "$report/build-mode.txt"
python3 tools/audit/inspect_source.py "$report"
cp lean-toolchain lake-manifest.json lakefile.toml "$report/"
{
  date -u +%FT%TZ
  git rev-parse HEAD
  uname -sm
  lake --version
  lake env lean --version
} 2>&1 | tee "$report/environment.txt"
if [[ "$mode" == --fresh ]]; then
  # Lake cleans the root package's generated build outputs, not source files.
  lake clean 2>&1 | tee "$report/clean.log"
fi
lake build 2>&1 | tee "$report/build.log"
lake env lean PrimeTensor.lean 2>&1 | tee "$report/root.log"
lake env lean tools/audit/Contracts.lean 2>&1 | tee "$report/contracts-and-axioms.log"
python3 tools/audit/inspect_source.py "$report/after" > "$report/after.log"
python3 - "$report" <<'PY'
import json, sys
from pathlib import Path
p = Path(sys.argv[1])
a = json.loads((p/'source-identity.json').read_text())
b = json.loads((p/'after/source-identity.json').read_text())
if a['head'] != b['head'] or a['input_digest'] != b['input_digest']:
    raise SystemExit('Source inputs changed during the baseline run; rerun on a stable tree.')
PY
