#!/usr/bin/env python3
"""Register strict physical temporal distributions and their solenoidal test bridge."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionBridge244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_regularTimeDistribution_apply244',
    'h3Path_physicalTestMomentum_locallyIntegrableOnStrict244',
    'h3Path_physicalTestSource_locallyIntegrableOnStrict244',
    'h3Path_distributionalMomentum_iff_timeTestMomentum244',
    'h3Path_timeTestMomentum_of_pressureNeutralTimeTests244',
    'h3Path_distributionalMomentum_of_pressureNeutralTimeTests244',
    'h3Path_timeTestPressureIntegral_eq_zero_of_snapshotwise244',
    'h3Path_distributionalMomentum_of_snapshotwisePressureTimeTests244',
)
DEFS = (
    'h3PathStrictTimeOpen244',
    'h3PathRegularTimeDistribution244',
    'h3PathPhysicalTestMomentumTime244',
    'h3PathPhysicalTestProjectedSourceTime244',
    'h3PathSolenoidalDistributionalMomentumOn244',
    'h3PathSolenoidalTimeTestMomentumOn244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Proof placeholder found')
    for kind, names in [('theorem', THEOREMS), ('def', DEFS)]:
        for name in names:
            if not re.search(r'^' + r'(?:noncomputable\s+)?' + kind + r'\s+' + re.escape(name) + r'\b', src, re.M):
                raise SystemExit(f'Missing {kind}: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    rest = [l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in rest:
                rest.append(command)
    result = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if result != original:
        AUDIT.write_text(result)
    print(f'Registered {len(DEFS)} definition(s) and {len(THEOREMS)} theorem(s)')

if __name__ == '__main__':
    main()
