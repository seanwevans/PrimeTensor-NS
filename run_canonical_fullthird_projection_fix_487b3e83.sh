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
  test "$(git rev-parse --short=8 HEAD)" = 487b3e83

  # Overwrite only the new uncommitted theorem source; preserve the other
  # previously extracted documentation and registration artifacts.
  unzip -o ~/Downloads/primetensor-canonical-fullthird-projection-fix-487b3e83.zip -d .

  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdCanonicalPhysicalBridge244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdCanonicalPhysicalBridge244
  python3 tools/audit/register_first_monomial_full_third_canonical_physical_bridge244.py
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
  git commit -m "construct canonical H3 full-third transport and isolate physical trace gaps"
  git push
  git log -1 --oneline | wl-copy
)
