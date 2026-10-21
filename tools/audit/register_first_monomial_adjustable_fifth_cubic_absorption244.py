#!/usr/bin/env python3
"""Register adjustable signed fifth/cubic Fourier absorption (base a9af178c)."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAdjustableFifthCubicAbsorption244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3_globalForcingTwoMoment_pointwise_adjustable244', 'h3Path_globalAbsoluteTransfer_le_adjustableFifthCubic244', 'h3Path_globalFourthRadialPairing_add_adjustableFifth_le_cubic244', 'h3Path_globalFourthRadialPairing_add_threeHalvesFifth_le_twoCubic244', 'h3Path_globalFourthRadialPairing_nonpos_of_adjustable_cubicBudget244', 'h3_adjustableFifthCubic_threshold_le_one244')


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
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
    for name in THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for chk in ('#check ' + fq, '#print axioms ' + fq):
            if chk not in body:
                body.append(chk)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print('Registered {} adjustable signed absorption declarations'.format(len(THEOREMS)))


if __name__ == '__main__':
    main()
