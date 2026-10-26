#!/usr/bin/env python3
"""Register the exact quadratic-sharp cubic PDE windows and three-scale barrier."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticSharpClock244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_cubicAnnulusQuadraticSharpPDEWidth_valid244', 'h3Path_quadraticSharpMin_smallCost_forces_threeCaps244', 'h3Path_exactQuadraticSharpClocks_vanishingThreeCapAlternative244', 'h3Path_quarterGap_quadraticClockLinearCap_forces_sixth244', 'h3Path_quarterGap_quadraticClockRootCap_forces_ninth244', 'h3Path_exactQuadraticSharpClocks_threeScaleBarrier244', 'h3Path_cubicHighSnapshot_has_quarterGapQuadraticSharpClock244', 'h3Path_noL2Trace_forces_quarterGapQuadraticSharpClocks244', 'h3Path_noL2Trace_finiteDissipation_quadraticSharpThreeScale244')
DEFINITIONS = ('h3PathCubicAnnulusQuadraticSharpPDEWidth244',)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unexpected unproven placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFINITIONS:
        if not re.search(r'^\s*noncomputable def\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith('import ')] + [imp]))
    rest = [ln for ln in lines if not ln.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFINITIONS + THEOREMS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + q, '#print axioms ' + q):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} theorems and {len(DEFINITIONS)} definition.')

if __name__ == '__main__':
    main()
