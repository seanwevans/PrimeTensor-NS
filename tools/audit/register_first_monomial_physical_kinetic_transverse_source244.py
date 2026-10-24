#!/usr/bin/env python3
"""Register the exact physical kinetic/transverse-source orthogonal decomposition."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticTransverseSource244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathPhysicalWeightedTransverseSource244',
    'h3PathPhysicalTransverseSource244',
)
THEOREMS = (
    'h3Path_physicalWeightedTransverse_orthogonal244',
    'h3Path_physicalTransverse_scaled_eq_weighted244',
    'h3Path_physicalTransverse_orthogonal244',
    'h3Path_physicalSource_pythagorean_transverse244',
    'h3Path_physicalRadialSource_norm_sq244',
    'h3Path_physicalSource_norm_sq_eq_transverse_add_kineticCost244',
    'h3Path_physicalKineticCost_sq_le_source_sq244',
    'h3Path_physicalKinetic_positive_of_positiveTerminal244',
    'h3Path_physicalSource_norm_sq_terminalTransverse244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Proof placeholder or axiom found')
    for kind, names in (('noncomputable def', DEFS), ('theorem', THEOREMS)):
        for name in names:
            if not re.search(r'^' + re.escape(kind) + r'\s+' + re.escape(name) + r'\b', source, re.M):
                raise SystemExit(f'Missing {kind}: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in DEFS + THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(DEFS)} definitions and {len(THEOREMS)} theorems.')

if __name__ == '__main__':
    main()
