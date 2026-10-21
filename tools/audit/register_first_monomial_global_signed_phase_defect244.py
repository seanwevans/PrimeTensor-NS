#!/usr/bin/env python3
"""Register the exact global fifth/cubic signed Fourier phase-defect bridge."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdGlobalSignedPhaseDefect244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3GlobalSignedPhaseDensity244',
    'h3PathTopFourierGlobalSignedPhaseDefect244',
)
THEOREMS = (
    'h3_globalSignedPhaseDensity_eq_twoDefects244',
    'h3_globalSignedPhaseDensity_ge_amplitudeMismatch244',
    'h3_globalSignedPhaseDensity_nonneg244',
    'h3Path_globalSignedPhaseDefect_nonneg244',
    'h3Path_globalSignedPhaseDefect_eq_fifth_add_cubic_sub_Leray244',
    'h3Path_globalFourthRadialPairing_add_fifth_add_phase_eq_cubic244',
    'h3Path_globalFourthRadialPairing_nonneg_forces_cubic_ge_fifth_add_phase244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Proof placeholder detected')
    for name in DEFS:
        if not re.search(r'^noncomputable def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {name}')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    out = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if out != old:
        AUDIT.write_text(out)
    print(f'Registered {len(DEFS)+len(THEOREMS)} signed global phase-defect declarations')


if __name__ == '__main__':
    main()
