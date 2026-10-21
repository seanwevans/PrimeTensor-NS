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
  test "$(git rev-parse --short=8 HEAD)" = 2d938161

  unzip -o \
    ~/Downloads/primetensor-fullthird-normalized-signed-channels-2d938161.zip \
    -d .

  python3 tools/audit/register_first_monomial_normalized_signed_channels244.py

  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedSignedChannels244.lean
  MODULE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedSignedChannels244

  lake env lean "$FILE"
  lake build "$MODULE"
  lake env lean tools/audit/FirstMonomialTriad.lean
  lake build

  git add -A
  git commit -m "normalize fixed cofinal signed H3 channels and extract high-rate sequences"
  git push
  git log -1 --oneline | wl-copy
)
