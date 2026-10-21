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
  test "$(git rev-parse --short=8 HEAD)" = 84f78866

  unzip -o \
    ~/Downloads/primetensor-fullthird-physical-gradient-linf-trace-proof-fix-84f78866.zip \
    -d .

  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientLinfTrace244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientLinfTrace244

  python3 tools/audit/register_first_monomial_full_third_physical_gradient_linf_trace244.py
  python3 proof/generate_index.py
  python3 proof/generate_index.py --check
  python3 proof/check_fragment.py --all

  lake build "$MODULE"
  lake env lean "$FILE"
  lake env lean tools/audit/FirstMonomialTriad.lean
  lake build
  bash tools/audit/baseline.sh --reuse-build

  git diff --check
  git add -A
  git commit -m "prove physical H3 gradient strong L2-L2-Linfty trace and triple limits"
  git push
  git log -1 --oneline | wl-copy
)
