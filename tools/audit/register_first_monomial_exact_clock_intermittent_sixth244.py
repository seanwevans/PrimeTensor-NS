#!/usr/bin/env python3
"""Register the intermittent sixth-order exact-clock obstruction."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
    'SpectralFiniteAnnulusPDEIntermittentSixthBarrier244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_exactCubicClocks_intermittentNoncompression_forces_sixthRate244',
    'h3Path_exactCubicClocks_boundedRateIndices_force_smallLag244',
    'h3Path_noL2Trace_finiteDissipation_intermittentSixthBarrier244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproven placeholder / axiom found')
    for theorem in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(theorem) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {theorem}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for theorem in THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + theorem
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} intermittent exact-clock theorems.')

if __name__ == '__main__':
    main()
