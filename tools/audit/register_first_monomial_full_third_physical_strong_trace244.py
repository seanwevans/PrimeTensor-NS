#!/usr/bin/env python3
"""Register matched real Schwartz strong physical second/third jets and full T3."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalStrongTrace244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = {
    'noncomputable def': (
        'h3MatchedSchwartzPhysicalSecondJetState244',
        'h3MatchedSchwartzPhysicalThirdJetState244',
    ),
    'theorem': (
        'h3MatchedSchwartzPhysicalSecondJetState_tendsto_actual244',
        'h3MatchedSchwartzPhysicalThirdJetState_tendsto_actual244',
        'h3MatchedSchwartz_physicalFirstJetGauge244',
        'h3MatchedSchwartz_physicalStrongTraceAndFullThird244',
        'exists_physicalSnapshot_matchedFullThirdAndStrongJets244',
    ),
}

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Lean placeholder found')
    for decl, names in DECLS.items():
        for name in names:
            if not re.search(r'^' + re.escape(decl) + r'\s+' + re.escape(name) + r'\b', src, re.M):
                raise SystemExit(f'Missing declaration: {decl} {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for names in DECLS.values():
        for name in names:
            qualified = 'PrimeTensor.FirstMonomialTriad.' + name
            for command in ('#check ' + qualified, '#print axioms ' + qualified):
                if command not in body:
                    body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print('Registered physical strong H3 jets and canonical full-third trace')

if __name__ == '__main__':
    main()
