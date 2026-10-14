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

  cd "$HOME/Repos/PrimeTensor-NS"
  git pull --ff-only
  test "$(git rev-parse --short=8 HEAD)" = '367c102d'

  unzip -o "$HOME/Downloads/primetensor-low-reality-phase-367c102d.zip" -d .

  python3 - <<'PY'
from pathlib import Path
old = 'import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowSharpness'
new = 'import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowRealityPhase'
main = Path('PrimeTensor.lean')
s = main.read_text()
assert old in s, 'expected sharpness import missing'
if new not in s:
    s = s.replace(old + '\n', old + '\n' + new + '\n', 1)
    main.write_text(s)

audit = Path('tools/audit/FirstMonomialTriad.lean')
s = audit.read_text()
assert s.startswith(old + '\n') or s.startswith(new + '\n'), 'unexpected audit import'
if s.startswith(old + '\n'):
    s = new + '\n' + s[len(old) + 1:]
checks = ['lowNormalAuditRealityPair_eq', 'lowNormalAuditRealityPair_re',
          'lowNormalAuditRealityPair_I_re', 'lowNormalAuditRealityPair_I_re_lower',
          'lowNormalAudit_no_uniform_quadratic_reality_phase_bound']
if '#check PrimeTensor.FirstMonomialTriad.' + checks[0] not in s:
    marker = '#print axioms PrimeTensor.FirstMonomialTriad.lowNormalAudit_no_uniform_quadratic_bound'
    assert s.rstrip().endswith(marker), 'audit checkpoint does not match'
    s = s.rstrip() + '\n\n'
    for name in checks:
        s += f'#check PrimeTensor.FirstMonomialTriad.{name}\n'
        s += f'#print axioms PrimeTensor.FirstMonomialTriad.{name}\n\n'
    audit.write_text(s)
PY

  FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowRealityPhase.lean
  lake env lean "$FILE"
  lake env lean tools/audit/FirstMonomialTriad.lean
  lake build
  git diff --check
  git add PrimeTensor.lean tools/audit/FirstMonomialTriad.lean \
    "$FILE" docs/research/first-monomial-triad-low-reality-phase.md
  git commit -m 'audit Fourier reality phase of sharp low-normal triad'
  git push
  git log -1 --oneline | wl-copy
)
