#!/usr/bin/env python3
"""Register terminal physical L2 trace from transverse source action."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticTerminalTransverseTrace244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('H3PhysicalTransverseTerminalTailVanishing244',)
THEOREMS = (
    'h3Path_physicalVelocity_uniformTerminalIncrementSmall_of_transverse244',
    'h3Path_physicalVelocity_existsTerminalL2Trace_of_transverse244',
    'h3Path_physicalVelocity_tendsto_zero_of_zeroTerminalKinetic244',
    'h3Path_physicalVelocity_existsTerminalL2Trace_of_transverseAllCases244',
    'h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244',
    'h3Path_physicalVelocity_terminalL2Trace_and_exactKineticMass244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Proof placeholder or axiom found')
    for decl in DEFS:
        if not re.search(r'^def\s+' + re.escape(decl) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {decl}')
    for decl in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(decl) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {decl}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith('import ')] + [imp]))
    rest = [ln for ln in lines if not ln.startswith('import ')]
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
