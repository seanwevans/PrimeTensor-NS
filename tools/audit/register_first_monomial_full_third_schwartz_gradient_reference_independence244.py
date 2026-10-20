#!/usr/bin/env python3
"""Register genuine Schwartz gradient reference-independence results."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientReferenceIndependence244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = {
    'theorem': (
        'fullSchwartzGradientSpectralPairEnvelope_cross_tendsto_zero244',
        'h3MatchedSchwartzGradientCompletion_limit_unique244',
        'exists_h3MatchedSchwartzGradientCompletion244',
        'weightedH3CanonicalGradientTransport_tendsto244',
    ),
    'structure': ('H3MatchedSchwartzGradientCompletion244',),
    'noncomputable def': ('weightedH3CanonicalGradientTransport244',),
}


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for keyword, names in DECLS.items():
        for name in names:
            if not re.search(r'^' + re.escape(keyword) + r'\s+' + re.escape(name) + r'\b', source, re.M):
                raise SystemExit('Missing Lean declaration: ' + keyword + ' ' + name)
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for names in DECLS.values():
        for name in names:
            qualified = 'PrimeTensor.FirstMonomialTriad.' + name
            for command in ('#check ' + qualified, '#print axioms ' + qualified):
                if command not in body:
                    body.append(command)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print('Registered Schwartz H3 canonical gradient reference-independence results')


if __name__ == '__main__':
    main()
