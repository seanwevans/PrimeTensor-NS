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
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowRealityPhase
  DOC=docs/research/first-monomial-triad-low-reality-phase.md

  test -f "$FILE"
  test -f "$DOC"
  grep -Fq "import $MODULE" PrimeTensor.lean
  grep -Fq "import $MODULE" tools/audit/FirstMonomialTriad.lean

  # Plain `lean` typechecks source but does NOT install an importable .olean.
  lake env lean "$FILE"
  # This creates the .olean that the audit imports.
  lake build "$MODULE"
  lake env lean tools/audit/FirstMonomialTriad.lean
  lake build

  git diff --check
  git add PrimeTensor.lean tools/audit/FirstMonomialTriad.lean "$FILE" "$DOC"
  git diff --cached --check
  git commit -m 'audit Fourier reality phase of sharp low-normal triad'
  git push
  git log -1 --oneline | wl-copy
)
