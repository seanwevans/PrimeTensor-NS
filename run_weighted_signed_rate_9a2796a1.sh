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
  test "$(git rev-parse --short=8 HEAD)" = 9a2796a1

  unzip -o \
    ~/Downloads/primetensor-fullthird-weighted-canonical-signed-rate-9a2796a1.zip \
    -d .

  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalCanonicalSignedRate244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalCanonicalSignedRate244

  python3 tools/audit/register_first_monomial_full_third_physical_canonical_signed_rate244.py
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
  git commit -m "transfer exact physical H3 signed energy rate to canonical weighted spectral cubic"
  git push
  git log -1 --oneline | wl-copy
)
