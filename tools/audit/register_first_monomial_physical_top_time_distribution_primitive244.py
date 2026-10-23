#!/usr/bin/env python3
"""Register the distributional derivative of the physical source primitive."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionPrimitive244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_scalarSourcePrimitive_hasDerivAt_onStrict244', 'h3Path_regularTimeDistribution_sourcePrimitive_deriv244', 'h3Path_physicalProjectedSourcePrimitive_distributionalDerivative244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Proof placeholder found')
    for theorem in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(theorem) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem {theorem}')
    imp = 'import ' + MODULE
    content = ROOT.read_text()
    if imp not in content.splitlines():
        ROOT.write_text(content.rstrip() + '\n' + imp + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    rest = [l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in rest:
                rest.append(command)
    out = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if out != original:
        AUDIT.write_text(out)
    print(f'Registered {len(THEOREMS)} theorems')

if __name__ == '__main__':
    main()
