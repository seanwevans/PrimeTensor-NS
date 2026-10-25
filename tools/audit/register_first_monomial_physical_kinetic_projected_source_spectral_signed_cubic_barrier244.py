#!/usr/bin/env python3
"""Register the physical high-energy or negative canonical-third channel barrier."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedCubicBarrier244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_signedThirdDeficit_largeAllowance_or_negativeCubic244',
    'h3Path_negativeCanonicalThird_gradient_or_interpolation244',
    'h3Path_adverseFullTransport_highEnergy_or_negativeCanonicalChannel244',
    'h3Path_highAllowance_forces_quadraticPhysicalEnergy244',
    'h3Path_physicalNoL2Trace_forces_signedCubicBarrierSequence244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    code = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', code, re.M):
        raise SystemExit('Unproven placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', code, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    rest = [x for x in lines if not x.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    output = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if output != old:
        AUDIT.write_text(output)
    print(f'Registered {len(THEOREMS)} sign-definite spectral cubic barrier theorems.')

if __name__ == '__main__':
    main()
