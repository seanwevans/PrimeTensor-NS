#!/usr/bin/env python3
"""Register kinetic-anchored essential negative H3 spectral channels."""
import re
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdKineticEssentialNegativeChannel244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathKineticAnchorSignedCost244',
    'h3PathKineticGradientAdverseRatio244',
    'h3PathKineticInterpolationAdverseRatio244',
)
THEOREMS = (
    'h3Path_kineticAnchor_signedCubic_normalizedGrowth244',
    'h3Path_unabsorbed_le_kineticSignedChannelRemainder244',
    'h3Path_kineticSignedChannels_no_joint_ae_integrable_majorants244',
    'h3Path_kineticSignedChannels_fixed_ae_integrableMajorantBarrier244',
    'h3Path_kineticSignedChannels_fixedEssentialHighRate244',
    'h3Path_extension_of_kineticSignedChannel_ae_integrableMajorants244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    # Match Lean tokens; avoid matching prose comments in documentation.
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
    print('Registered kinetic-anchored essential negative spectral channels')

if __name__ == '__main__':
    main()
