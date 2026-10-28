#!/usr/bin/env python3
"""Register canonical critical-width cofinal escape obstructing continuation."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalRegimeFailure244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_scalar_notEventuallyLe_cofinalStrictViolation244',
    'h3Path_scalar_notEventuallyTriple_cofinalFailure244',
    'h3Path_noL2Trace_noExtension_canonicalCriticalRegimeCofinalFailure244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', src, re.M):
        raise SystemExit('Source contains unproved placeholder or axiom')
    for theorem in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(theorem) + r'\b', src, re.M):
            raise SystemExit(f'Missing theorem {theorem}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    rest = [s for s in lines if not s.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for theorem in THEOREMS:
        q = 'PrimeTensor.FirstMonomialTriad.' + theorem
        for cmd in ('#check ' + q, '#print axioms ' + q):
            if cmd not in rest:
                rest.append(cmd)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if new != original:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} canonical critical-regime failure theorems.')

if __name__ == '__main__':
    main()
