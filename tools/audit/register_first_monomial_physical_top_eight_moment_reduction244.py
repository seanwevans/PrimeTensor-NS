#!/usr/bin/env python3
"""Register the eighth-moment reduction under uniform low Fourier ceilings."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopEightMomentReduction244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_orderEightPrimitive_two_eq_velocityMoment244',
    'h3Path_orderEightPrimitive_five_eq_velocityMoment244',
    'h3_orderEightVelocityPairPrimitive_lowBound244',
    'h3Path_unboundedPhysicalTop_forces_eightMoment_of_lowPrimitiveCeiling244',
    'h3Path_unboundedPhysicalTop_forces_eightMoment_of_lowFourierCeiling244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Lean proof placeholder detected')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    newer = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if newer != old:
        AUDIT.write_text(newer)
    print('Registered', len(THEOREMS), 'eighth-moment reduction declarations')

if __name__ == '__main__':
    main()
