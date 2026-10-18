#!/usr/bin/env python3
"""Idempotently register axis/Hilbert coherent-sector disjointness and support."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorGeometry244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullCoherentPairIndex_injective244',
    'thirdFullSixAxisCenters_coordinate_gap244',
    'thirdFullSixAxisCenters_dist_gap244',
    'thirdFullCoherentPairLabel_dist_gap244',
    'thirdFullCoherentAxisBalls_disjoint244',
    'thirdFullHilbertCoherentSectors_disjoint244',
    'thirdFullAxisImagKernel_mem_labeled_sector244',
    'thirdFullAxisImagKernel_zero_off_labeled_sectors244',
    'thirdFullAxisSectorGeometry_exists_radius244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    s = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in s:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    body = [l for l in lines if not l.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {q}', f'#print axioms {q}'):
            if check not in body:
                body.append(check)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered twelve-sector axis separation, physical disjointness and support')

if __name__ == '__main__':
    main()
