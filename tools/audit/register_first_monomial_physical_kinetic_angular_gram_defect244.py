#!/usr/bin/env python3
"""Register physical source Gram determinant and exact angular rate identity."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularGramDefect244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('h3PathPhysicalSourceGramDefect244',)
THEOREMS = (
    'h3Path_physicalSourceGram_eq_kinetic_mul_transverse_sq244',
    'h3Path_physicalSourceGram_nonneg244',
    'h3Path_physicalSourceGram_eq_zero_iff_transverse_eq_zero244',
    'h3Path_physicalSourceGram_eq_zero_iff_pureLongitudinal244',
    'h3Path_physicalAngularRate_energy_mul_norm_sq244',
    'h3Path_physicalSourceGram_eq_energy_sq_mul_unitVelocity_deriv_sq244',
    'h3Path_physicalSourceGram_eq_zero_iff_angularDeriv_eq_zero244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Proof placeholder or axiom found')
    for name in DEFS:
        if not re.search(r'^noncomputable def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {name}')
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
    print(f'Registered {len(DEFS)} definition and {len(THEOREMS)} theorems.')

if __name__ == '__main__':
    main()
