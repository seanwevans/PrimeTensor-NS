#!/usr/bin/env python3
"""Register global zero-radius spectral heat/Leray decomposition."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalZeroCutoff244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('h3PathTopFourierGlobalHeatRate244', 'h3PathTopFourierGlobalLerayRate244', 'h3PathTopFourierGlobalDiffusionExcess244', 'h3PathTopFourierGlobalNonlinearExcess244')
THEOREMS = ('h3Path_zeroRadialBelow_eq_empty244', 'h3Path_zeroRadialRestrict_inner_eq_global244', 'h3Path_globalHeatRate_nonpos244', 'h3Path_fourthRadialPairing_eq_globalHeat_add_Leray244', 'h3Path_signedExcess_eq_globalHeat_add_Leray244', 'h3Path_normalizedExcessRate_eq_globalHeat_add_Leray244', 'h3Path_nearYoung_forces_globalHeat_Leray_secant244')


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
        for chk in ('#check ' + fq, '#print axioms ' + fq):
            if chk not in body:
                body.append(chk)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print('Registered {} global zero-cutoff Fourier declarations'.format(len(DEFS)+len(THEOREMS)))


if __name__ == '__main__':
    main()
