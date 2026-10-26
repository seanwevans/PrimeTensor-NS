#!/usr/bin/env python3
"""Register physical exact cubic-clock concentration alternative."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEExactClockConcentration244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_strictMonoCubicHeight_eventually_above_mass244', 'h3Path_exactCubicClocks_finiteCosts_forces_alternative244', 'h3Path_noL2Trace_finiteDissipation_exactPDEClockConcentration244')
DEFINITIONS = ('h3PathCubicAnnulusActualGap244', 'h3PathCubicAnnulusActualLinearRate244', 'h3PathCubicAnnulusActualQuadraticRate244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Unproven placeholder/axiom found')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFINITIONS:
        if not re.search(r'^\s*noncomputable def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {name}')
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
    for name in DEFINITIONS + THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} exact-clock concentration theorems and {len(DEFINITIONS)} definitions.')

if __name__ == '__main__':
    main()
