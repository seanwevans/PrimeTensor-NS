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
  test "$(git rev-parse --short=8 HEAD)" = 52af3e57

  unzip -o \
    ~/Downloads/primetensor-fullthird-physical-second-l4-audit-import-fix-52af3e57.zip \
    -d .

  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSecondL4Identification244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSecondL4Identification244

  python3 tools/audit/register_first_monomial_full_third_physical_second_l4_identification244.py
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
  git commit -m "identify physical H3 second jets with canonical L4 trace"
  git push
  git log -1 --oneline | wl-copy
)
