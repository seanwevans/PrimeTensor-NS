#!/usr/bin/env python3
"""Register actual radial spectral low-mass bounds and high-remainder escape."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralRadialMassEscape244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'h3PathActualSpectralLowRadialSquareMass244'),
    ('def', 'h3PathActualSpectralHighRadialRemainder244'),
    ('theorem', 'h3Path_actualSpectralLowRadialSquareMass_le_rawSquare244'),
    ('theorem', 'h3Path_actualSpectralLowRadialSquareMass_ceiling244'),
    ('theorem', 'h3Path_spectralCoordinateSquare_le_totalSquareEnergy244'),
    ('theorem', 'h3Path_fixedSpectralCoordinateEscape_forces_highRadialRemainder244'),
    ('theorem', 'h3Path_physicalNoL2Trace_forces_highRadialRemainder_of_rawCeiling244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproven placeholder or axiom found')
    for kind, name in DECLS:
        if not re.search(r'^\s*(?:noncomputable\s+)?' + kind + r'\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for _, name in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != AUDIT.read_text():
        AUDIT.write_text(updated)
    print(f'Registered {len(DECLS)} radial spectral mass declarations.')

if __name__ == '__main__':
    main()
