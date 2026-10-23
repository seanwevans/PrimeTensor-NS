#!/usr/bin/env python3
"""Register the compact-time-test span / homogeneous distribution kernel bridge."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionKernelSpan244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLARATIONS = (
    ('def', 'h3PathCompactTimeTestDerivativeSpan244'),
    ('theorem', 'h3Path_compactTimeTestSpan_of_normalizedBump_and_zeroMassPrimitive244'),
    ('theorem', 'h3Path_zeroDistributionDerivative_eq_constant_of_compactSpan244'),
    ('theorem', 'h3Path_physicalFTCDefect_constantDistribution_of_compactSpan244'),
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing: {p}')
    source = SOURCE.read_text()
    stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b', stripped):
        raise SystemExit('Proof placeholder found')
    for kind, name in DECLARATIONS:
        if not re.search(r'^' + kind + r'\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for _, name in DECLARATIONS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + qualified, '#print axioms ' + qualified):
            if cmd not in rest:
                rest.append(cmd)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(DECLARATIONS)} homogeneous distribution kernel declarations.')

if __name__ == '__main__':
    main()
