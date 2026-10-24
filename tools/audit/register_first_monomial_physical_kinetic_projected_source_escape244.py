#!/usr/bin/env python3
"""Register physical angular-speed coercivity and projected PDE source escape."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceEscape244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_physicalTransverse_norm_le_projectedSource244',
    'h3Path_physicalAngularSpeed_mul_terminalSqrt_le_transverse244',
    'h3Path_physicalAngularSpeed_mul_terminalSqrt_le_projectedSource244',
    'h3Path_physicalTransverseSource_cofinally_unbounded_of_noTrace244',
    'h3Path_physicalProjectedSource_cofinally_unbounded_of_noTrace244',
    'h3Path_physicalLaplacianMinusLeray_cofinally_unbounded_of_noTrace244',
    'h3Path_physicalL2Trace_of_projectedSource_ceiling244',
    'h3Path_physicalL2Trace_or_cofinalProjectedPDEsourceEscape244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Proof placeholder or axiom found')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
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
    print(f'Registered {len(THEOREMS)} projected-source escape theorems.')

if __name__ == '__main__':
    main()
