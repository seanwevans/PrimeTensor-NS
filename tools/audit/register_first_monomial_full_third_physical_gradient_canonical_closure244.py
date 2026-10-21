#!/usr/bin/env python3
"""Register physical H3 3-3-1 gradient/canonical completion in root and audit."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientCanonicalClosure244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = ('h3PhysicalGradientAxis_eq_fourTriples244', 'h3MatchedSchwartz_gradientAxis_tendsto_oldPhysical244', 'h3PhysicalGradient_sumAxisPairing244', 'h3MatchedSchwartz_gradientTransport_tendsto_oldPhysical244', 'h3PhysicalGradient_eq_weightedCanonical244', 'h3PhysicalFullThird_eq_weightedCanonical244')
DEFS = ('h3PhysicalGradientFourTripleSum244',)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for keyword, declarations in [('theorem', THEOREMS), ('noncomputable def', DEFS)]:
        for declaration in declarations:
            if not re.search(r'^' + keyword + r'\s+' + re.escape(declaration) + r'\b', source, re.M):
                raise SystemExit(f'Missing declaration: {declaration}')
    imp = 'import ' + MODULE
    old_root = ROOT.read_text()
    if imp not in old_root.splitlines():
        ROOT.write_text(old_root.rstrip() + '\n' + imp + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    rest = [x for x in lines if not x.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for declaration in (*THEOREMS, *DEFS):
        full = 'PrimeTensor.FirstMonomialTriad.' + declaration
        for line in ('#check ' + full, '#print axioms ' + full):
            if line not in rest:
                rest.append(line)
    result = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if result != old:
        AUDIT.write_text(result)
    print('Registered physical full-third H3 gradient/canonical identity')

if __name__ == '__main__':
    main()
