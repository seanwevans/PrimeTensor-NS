#!/usr/bin/env python3
"""Register the physical kinetic source-cost and dissipation corridor proofs."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticSourceCostCorridor244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_physicalSourcePairing_abs_eq_dissipation0_positiveTime244',
    'h3Path_dissipation0_le_physicalVelocity_mul_source_positiveTime244',
    'h3Path_dissipation0_le_sqrtKinetic_mul_source_positiveTime244',
    'h3Path_physicalSource_zero_implies_dissipation0_zero_positiveTime244',
    'h3Path_dissipation0_integral_le_half_initialKinetic_positiveTimes244',
    'h3Path_persistentDissipation0_floor_cost_positiveTimes244',
    'h3Path_exists_subcriticalDissipation0_witness_positiveTimes244',
    'h3Path_terminalMidpoint_subcriticalDissipation0_witness244',
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
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
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
    print(f'Registered {len(THEOREMS)} theorems.')

if __name__ == '__main__':
    main()
