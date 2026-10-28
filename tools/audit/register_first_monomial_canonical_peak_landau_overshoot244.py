#!/usr/bin/env python3
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakLandauOvershoot244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_scalarLandauSpike_energyOvershoot_or_slowClock244',
    'h3Path_physicalTransportSpike_energyOvershoot_or_slowClock244',
    'h3Path_physicalTransportSpike_forces_energyOvershoot_of_fastClock244',
    'h3Path_optimizedPeak_terminalCompression_or_transportLandauOvershoot244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    src = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', src, re.M):
        raise SystemExit('Placeholder or new axiom in source')
    for theorem in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(theorem) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem: {theorem}')
    imp = 'import ' + MODULE
    rows = ROOT.read_text().splitlines()
    if imp not in rows:
        ROOT.write_text('\n'.join(rows + [imp]) + '\n')
    rows = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in rows if x.startswith('import ')] + [imp]))
    rest = [x for x in rows if not x.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for theorem in THEOREMS:
        name = 'PrimeTensor.FirstMonomialTriad.' + theorem
        for line in ('#check '+name, '#print axioms '+name):
            if line not in rest:
                rest.append(line)
    revised = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if revised != AUDIT.read_text():
        AUDIT.write_text(revised)
    print(f'Registered {len(THEOREMS)} canonical Landau overshoot theorems.')
if __name__ == '__main__':
    main()
