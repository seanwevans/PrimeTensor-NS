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
  test "$(git rev-parse --short=8 HEAD)" = 8f1b40b5
  unzip -o ~/Downloads/primetensor-fullthird-physical-signed-slots-fix3-8f1b40b5.zip -d .
  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedSlotIntegrability244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedSlotIntegrability244
  python3 tools/audit/register_first_monomial_full_third_physical_signed_slot_integrability244.py
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
  git commit -m "prove physical H3 signed 243-slot Holder integrability and canonical representative invariance"
  git push
  git log -1 --oneline | wl-copy
)
