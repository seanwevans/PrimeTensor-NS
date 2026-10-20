#!/usr/bin/env python3
"""Register actual physical signed 243-slot integral equals weighted Schwartz limit.

Preserve the import-only root's original layout, and keep every audit import
in the opening header. Repeated registration is byte-for-byte idempotent.
"""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedCanonicalLimit244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3CanonicalSignedLpTriple_eq_integral244',
    'h3CanonicalSignedLpTriple_tendsto244',
    'h3MatchedSchwartz_signedSlotIntegral_tendsto_physical244',
    'h3MatchedSchwartz_allSignedSlots_tendsto_physical244',
    'h3PathCanonicalFirstMonomialAggregate_eq_weightedCanonicalSigned244',
    'h3PathCanonical_signedGap_eq_zero244',
)
DEFS = ('h3CanonicalSignedLpTriple244',)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for kw, decls in [('theorem', THEOREMS), ('noncomputable def', DEFS)]:
        for name in decls:
            if not re.search('^'+kw+r'\s+'+re.escape(name)+r'\b', source, re.M):
                raise SystemExit(f'Missing {kw}: {name}')
    statement = 'import ' + MODULE
    root_old = ROOT.read_text()
    root_lines = root_old.splitlines()
    if statement not in root_lines:
        ROOT.write_text(root_old.rstrip() + '\n' + statement + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [statement]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for decl in (*THEOREMS, *DEFS):
        qualified = 'PrimeTensor.FirstMonomialTriad.' + decl
        for line in ('#check ' + qualified, '#print axioms ' + qualified):
            if line not in body:
                body.append(line)
    revised = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if revised != old:
        AUDIT.write_text(revised)
    print('Registered 243-slot physical/canonical signed limit, with axiom audit')


if __name__ == '__main__':
    main()
