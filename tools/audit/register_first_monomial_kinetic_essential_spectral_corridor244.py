#!/usr/bin/env python3
"""Register the kinetic-anchored essential top-frequency Landau corridor."""
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdKineticEssentialSpectralCorridor244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('h3PathKineticTopLandauMargin244',)
THEOREMS = (
    'h3Path_kineticSignedAdverseSum_le_topLandauMargin244',
    'h3Path_kineticAnchor_normalizedGrowth_le_topLandauMargin244',
    'h3Path_unabsorbed_le_kineticTopLandauRemainder244',
    'h3Path_kineticTopLandauMargin_not_ae_integrableMajorant244',
    'h3Path_kineticTopLandau_essentialFrequencyCorridor244',
    'h3Path_extension_of_ae_integrable_topLandauMargin_majorant244',
    'h3Path_extension_of_ae_topSpectralDissipationDominance244',
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
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in ('#check ' + fq, '#print axioms ' + fq):
            if check not in body:
                body.append(check)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print('Registered kinetic essential top-frequency Landau corridor')


if __name__ == '__main__':
    main()
