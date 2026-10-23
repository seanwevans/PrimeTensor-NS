#!/usr/bin/env python3
"""Register the compact physical momentum-term bound and obstruction bridge."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopCompactMomentumTerms244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Preterminal_compactTemporalDomination_of_momentumTermsBound244',
    'h3Path_shortWindowTemporalDomination_of_momentumTermsBound244',
    'h3Path_physicalEighthMoments_of_momentumTermsBound244',
    'h3Path_unboundedPhysicalTop_forces_lower_or_eight_of_momentumTermsBound244',
    'h3Path_unboundedPhysicalTop_forces_lower_or_eight_or_momentumCompactFailure244',
)
DEFS = (
    'h3PreterminalMomentumTermsCompactBoundOnElapsed244',
    'h3PathVelocityShortWindowMomentumTermsBoundAt244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Proof placeholder found')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFS:
        if not re.search(r'^def\s+' + re.escape(name) + r'\b', src, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in rest:
                rest.append(command)
    output = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if output != original:
        AUDIT.write_text(output)
    print(f'Registered {len(DEFS)} definitions and {len(THEOREMS)} theorems')


if __name__ == '__main__':
    main()
