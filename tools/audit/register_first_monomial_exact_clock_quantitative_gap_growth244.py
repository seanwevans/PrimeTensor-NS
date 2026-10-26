#!/usr/bin/env python3
"""Register the quantitative quarter-gap / super-sixth cubic PDE-clock theorems."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
    'SpectralFiniteAnnulusPDEQuantitativeGapGrowth244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_cubicHighSnapshot_has_quarterGapExactPDEClock244',
    'h3Path_exactCubicClocks_quarterGapNoncompression_forces_superSixth244',
    'h3Path_noL2Trace_forces_quarterGapExactPDEClocks244',
    'h3Path_noL2Trace_finiteDissipation_quarterGapSuperSixth244',
)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', source, re.M):
        raise SystemExit('Unproven placeholder or axiom in theorem source')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing expected theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    rest = [l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + qualified, '#print axioms ' + qualified):
            if cmd not in rest:
                rest.append(cmd)
    content = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print(f'Registered {len(THEOREMS)} quarter-gap / super-sixth theorems.')


if __name__ == '__main__':
    main()
