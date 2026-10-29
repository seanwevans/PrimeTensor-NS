#!/usr/bin/env python3
"""Register canonical unconditional inner cutoff high-tail higher moment escape."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorUnconditionalInnerHigherEscape244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3Path_scalar_annulus_le_innerHighTail244', 'h3Path_exactAnchor_innerHighTail_cubicFloor244', 'h3Path_exactAnchor_innerCubic_forces_topHigherMoment244', 'h3Path_scalar_cubicLower_forces_allTopMomentEscape244', 'h3Path_noL2Trace_exactAnchor_unconditionalInnerHigherEscape244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Proof placeholder or axiom prohibited')
    for name in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    existing = AUDIT.read_text()
    lines = existing.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in THEOREMS:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + full, '#print axioms ' + full):
            if cmd not in rest:
                rest.append(cmd)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != existing:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} canonical unconditional inner-high escape theorems')

if __name__ == '__main__':
    main()
