#!/usr/bin/env python3
"""Register normalized physical H3 dissipation clocks from moving spectral mass."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
    'SpectralNormalizedDissipationClock244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_dominantRadialMass_forces_cubicDissipationEnergyClock244',
    'h3Path_cubicDissipationEnergyClock_forces_ratio_gt_radius244',
    'h3Path_physicalNoL2Trace_forces_normalizedDissipationClockSequence244',
    'h3Path_physicalNoL2Trace_forces_normalizedDissipationRatioDivergence244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproven placeholder or axiom found')
    for name in THEOREMS:
        if not re.search(r'^\s*(?:noncomputable\s+)?theorem\s+'
                         + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
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
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} normalized physical dissipation clock theorems.')


if __name__ == '__main__':
    main()
