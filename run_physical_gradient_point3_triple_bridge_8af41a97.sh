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
  test "$(git rev-parse --short=8 HEAD)" = 8af41a97
  unzip -o ~/Downloads/primetensor-fullthird-physical-gradient-point3-triple-8af41a97.zip -d .
  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientPoint3TripleBridge244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientPoint3TripleBridge244
  python3 tools/audit/register_first_monomial_full_third_physical_gradient_point3_triple_bridge244.py
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
  git commit -m 'identify physical H3 gradient L2-L2-Linfty triples with old Point3 integrals'
  git push
  git log -1 --oneline | wl-copy
)
