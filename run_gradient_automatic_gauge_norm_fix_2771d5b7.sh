#!/usr/bin/env bash
(
  set -euxo pipefail
  pause_on_failure() {
    local rc=$?
    if (( rc != 0 )); then
      printf '\nStopped with exit code %s.\n' "$rc"
      read -r -p 'Press Enter to close... ' _
    fi
  }
  trap pause_on_failure EXIT
  cd ~/Repos/PrimeTensor-NS
  git pull --ff-only
  test "$(git rev-parse --short=8 HEAD)" = 2771d5b7
  unzip -o ~/Downloads/primetensor-schwartz-gradient-automatic-gauge-norm-fix-2771d5b7.zip -d .
  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientAutomaticGauge244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientAutomaticGauge244
  python3 tools/audit/register_first_monomial_full_third_schwartz_gradient_automatic_gauge244.py
  python3 proof/generate_index.py
  python3 proof/generate_index.py --check
  python3 proof/check_fragment.py --all
  lake env lean "$FILE"
  lake build "$MODULE"
  lake env lean tools/audit/FirstMonomialTriad.lean
  lake build
  bash tools/audit/baseline.sh --reuse-build
  git diff --check
  git add -A
  git commit -m "derive full 972 gradient gauge vanishing from H3 energy Cauchy"
  git push
  git log -1 --oneline | wl-copy
)
