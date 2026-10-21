#!/usr/bin/env python3
"""Register physical signed excess: radial-tail heat, Leray, and low complement."""
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedExcessRadialTailLow244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('h3PathTopFourierLowRadialComplement244', 'h3PathTopFourierTailDiffusionBackground244', 'h3PathTopFourierTailNonlinearExcess244', 'h3PathTopFourierLowRadialDerivativeCorrection244')
THEOREMS = ('h3Path_topFourierLowRadialComplement_hasDerivAt244', 'h3Path_fourthRadialPairing_eq_tailHeat_add_transfer_add_low244', 'h3Path_signedExcess_eq_tailHeat_add_Leray_add_low244', 'h3Path_normalizedExcessRate_eq_tailHeat_add_Leray_add_low244', 'h3Path_nearYoung_forces_tailHeat_Leray_low_secant244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
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
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print('Registered exact high radial PDE balance and low complement in Fourier excess')

if __name__ == '__main__':
    main()
