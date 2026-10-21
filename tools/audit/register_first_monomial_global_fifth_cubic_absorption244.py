#!/usr/bin/env python3
"""Register the signed global fifth/cubic absorption and forcing criterion."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdGlobalFifthCubicAbsorption244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_globalLerayRate_eq_zeroTailTransfer244',
    'h3Path_globalLerayRate_le_fullAbsoluteTransfer244',
    'h3Path_globalHeatRate_eq_negTwoFifthMass244',
    'h3Path_globalFourthRadialPairing_add_fifth_le_cubic244',
    'h3Path_globalFourthRadialPairing_nonpos_of_cubic_le_fifth244',
    'h3Path_globalFourthRadialPairing_pos_forces_cubic_gt_fifth244',
    'h3Path_globalFourthRadialPairing_le_negRemainingFifth244',
    'h3Path_globalFourthRadialPairing_strictNeg_of_cubic_fraction244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Proof placeholder detected')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in body:
                body.append(command)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print(f'Registered {len(THEOREMS)} signed global fifth/cubic absorption theorems')

if __name__ == '__main__':
    main()
