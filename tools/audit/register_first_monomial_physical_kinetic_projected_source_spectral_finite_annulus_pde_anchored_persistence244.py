#!/usr/bin/env python3
"""Register anchored projected-PDE finite-annulus persistence proofs."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
          'SpectralFiniteAnnulusPDEAnchoredPersistence244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_lowRadialMultiplier_anchoredQuadraticStability244',
    'h3Path_lowRadialDissipation_anchoredGradientStability244',
    'h3Path_lowRadialPDEGradientRate_nonneg244',
    'h3Path_actualLowRadialDissipationVariation_anchoredPDE244',
    'h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244',
    'h3Path_actualFiniteAnnulusVariation_anchoredPDE244',
    'h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244',
)
DEFS = (
    'h3PathLowRadialPDEGradientRate244',
    'h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    contents = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', contents, re.M):
        raise SystemExit('Unproven placeholder or axiom found')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', contents, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFS:
        if not re.search(r'^\s*noncomputable def\s+' + re.escape(name) + r'\b', contents, re.M):
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
    for name in (*DEFS, *THEOREMS):
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    update = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if update != old:
        AUDIT.write_text(update)
    print(f'Registered {len(THEOREMS)} anchored annular PDE theorems and {len(DEFS)} definitions.')

if __name__ == '__main__':
    main()
