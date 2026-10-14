#!/usr/bin/env bash
(
  set -euxo pipefail
  pause_on_failure() {
    local rc=$?
    if (( rc != 0 )); then
      printf '\nStopped with exit code %s.\n' "$rc"
      read -r -p 'Press Enter to close... ' _ || true
    fi
  }
  trap pause_on_failure EXIT

  cd "$HOME/Repos/PrimeTensor-NS"
  test "$(git rev-parse --short=8 HEAD)" = '367c102d'

  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowRealityPhase.lean
  DOC=docs/research/first-monomial-triad-low-reality-phase.md
  AUDIT=tools/audit/FirstMonomialTriad.lean

  test -f "$FILE"
  test -f "$DOC"
  test -f "$AUDIT"

  # Remove extra blank/whitespace-only lines at EOF; preserve one final newline.
  python3 - <<'PY'
from pathlib import Path
p = Path('tools/audit/FirstMonomialTriad.lean')
s = p.read_text()
p.write_text(s.rstrip() + '\n')
PY

  # The previous run already compiled the audit and all 22,675 build jobs.
  git diff --check
  git add PrimeTensor.lean "$AUDIT" "$FILE" "$DOC"
  git diff --cached --check
  git commit -m 'audit Fourier reality phase of sharp low-normal triad'
  git push
  git log -1 --oneline
  git log -1 --oneline | wl-copy
)
