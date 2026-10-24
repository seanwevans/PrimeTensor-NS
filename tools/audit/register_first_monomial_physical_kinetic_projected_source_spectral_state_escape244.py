#!/usr/bin/env python3
"""Register actual weighted H3 spectral-state source majorants and terminal alternative."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralStateEscape244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_physicalLaplacian_norm_le_actualSpectralState244',
    'h3Path_physicalLeray_norm_le_actualSpectralState_sq244',
    'h3Path_physicalProjectedSource_norm_le_actualSpectralGrowth244',
    'h3Path_cofinalNormEscape_forces_spectralNorm_linear244',
    'h3Path_cofinalNormEscape_forces_spectralNorm_quadratic244',
    'h3Path_physicalLaplacian_cofinalEscape_forces_spectralState244',
    'h3Path_physicalLeray_cofinalEscape_forces_spectralState244',
    'h3Path_physicalProjectedSource_cofinalEscape_forces_spectralState244',
    'h3Path_physicalSpectralState_cofinally_unbounded_of_noL2Trace244',
    'h3Path_physicalL2Trace_of_actualSpectralState_ceiling244',
    'h3Path_physicalL2Trace_or_actualSpectralStateCofinalEscape244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproven placeholder or axiom found')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} actual spectral-state escape theorems.')

if __name__ == '__main__':
    main()
