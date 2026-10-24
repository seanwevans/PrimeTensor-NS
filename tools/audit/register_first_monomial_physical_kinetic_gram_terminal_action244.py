#!/usr/bin/env python3
"""Register scalar physical Gram action identities and conditional terminal traces."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticGramTerminalAction244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('H3PhysicalGramTerminalTailVanishing244',)
THEOREMS = (
    'h3Path_physicalSourceGram_sqrt_eq_sqrtKinetic_mul_transverseNorm244',
    'h3Path_physicalSourceGram_sqrt_div_sqrtKinetic_eq_transverseNorm244',
    'h3Path_physicalSourceGram_sqrt_div_kinetic_eq_angularSpeed244',
    'h3Path_physicalGramAction_integral_eq_transverseAction244',
    'h3Path_physicalGramTailVanishing_iff_transverseTailVanishing244',
    'h3Path_physicalVelocity_terminalL2Trace_of_GramAction244',
    'h3Path_physicalUnitVelocity_terminalUnitTrace_of_GramAction244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Proof placeholder or axiom found')
    for name in DEFS:
        if not re.search(r'^def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing predicate: {name}')
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
    for name in DEFS + THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(DEFS)} predicate and {len(THEOREMS)} theorems.')

if __name__ == '__main__':
    main()
