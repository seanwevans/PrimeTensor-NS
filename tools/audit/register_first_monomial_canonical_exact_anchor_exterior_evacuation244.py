#!/usr/bin/env python3
"""Register exact canonical source-driven exterior H3 dissipation evacuation."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorExteriorEvacuation244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_physicalFiniteAnnulus_exteriorPartition244',
    'h3Path_scalar_cliff_forces_exteriorLoss244',
    'h3Path_physicalPDE_cliff_forces_exteriorEvacuation244',
    'h3Path_exactAnchorPDE_dip_forces_exteriorEvacuation244',
    'h3Path_noL2Trace_exactAnchor_persistentCharge_exteriorEvacuation244',
)
DEFS = ('h3PathFiniteAnnulusPhysicalExterior244',)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproved placeholder or axiom')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFS:
        if not re.search(r'^noncomputable def\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    existing = AUDIT.read_text()
    lines = existing.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFS + THEOREMS:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + full, '#print axioms ' + full):
            if cmd not in rest:
                rest.append(cmd)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != existing:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} theorems and {len(DEFS)} definitions')


if __name__ == '__main__':
    main()
