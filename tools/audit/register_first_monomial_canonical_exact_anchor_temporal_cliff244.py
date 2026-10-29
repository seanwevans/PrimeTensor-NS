#!/usr/bin/env python3
"""Register canonical exact-anchor full physical H3 dissipation temporal cliffs."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorTemporalCliff244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_scalar_smallPhysicalMass_peakChargeOrRelativeMean244',
    'h3Path_physicalIntegral_small_forces_relativeDissipationDip244',
    'h3Path_physicalVanishingWindowMass_chargeOrTemporalDip244',
    'h3Path_physicalPersistentAnchorCharge_forces_temporalCliff244',
    'h3Path_noL2Trace_exactAnchor_physicalTemporalCliffAlternative244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproved placeholder or axiom')
    for th in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(th) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {th}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    rest = [s for s in lines if not s.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for th in THEOREMS:
        fullname = 'PrimeTensor.FirstMonomialTriad.' + th
        for cmd in ('#check ' + fullname, '#print axioms ' + fullname):
            if cmd not in rest:
                rest.append(cmd)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if old != new:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} canonical H3 temporal-cliff theorems')

if __name__ == '__main__':
    main()
