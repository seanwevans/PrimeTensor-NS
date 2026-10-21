#!/usr/bin/env python3
"""Register physical signed-excess diffusion/transport splitting and transport burden."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSignedExcessDiffusionTransport244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathTopFourierDiffusionHilbertBackground244',
    'h3PathTopFourierNonlinearTransportExcess244',
)
THEOREMS = (
    'h3Path_signedExcess_eq_diffusionHilbert_add_transport244',
    'h3Path_nonlinearTransportExcess_eq_orderTwo244',
    'h3Path_normalizedExcessRate_eq_diffusionHilbert_add_transport244',
    'h3Path_nearYoung_forces_diffusionTransportSecant244',
    'h3Path_nearYoung_forces_nonlinearTransport_after_backgroundCeiling244',
    'h3Path_nearYoung_forces_orderTwoTransport_after_backgroundCeiling244',
)

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
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in ('#check ' + fq, '#print axioms ' + fq):
            if check not in body:
                body.append(check)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print('Registered exact physical signed-excess diffusion/transport and order-two transport burden')

if __name__ == '__main__':
    main()
