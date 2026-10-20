#!/usr/bin/env python3
"""Register canonical strong 27-coordinate L4 second-jet trace and independence."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdCanonicalSecondL4Trace244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = {
    'theorem': (
        'h3RealSchwartz_norm_toLp_four_eq_root244',
        'h3RealSchwartz_toLp_four_sub244',
        'h3RealSchwartz_secondJet_L4dist_eq_root244',
        'h3MatchedSchwartz_secondJet_L4_cauchy244',
        'h3MatchedSchwartz_secondJet_L4_tendsto244',
        'h3MatchedSchwartz_secondJet_L4_limit_unique244',
        'weightedH3CanonicalSecondJetL4Trace_tendsto244',
        'weightedH3CanonicalSecondJetL4Trace_family_tendsto244',
    ),
    'noncomputable def': (
        'h3MatchedSchwartz_secondJet_L4_limit244',
        'weightedH3CanonicalSecondJetL4Trace244',
    ),
}

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Lean proof placeholder found')
    for keyword, names in DECLS.items():
        for name in names:
            if not re.search(r'^' + re.escape(keyword) + r'\s+' + re.escape(name) + r'\b', src, re.M):
                raise SystemExit(f'Missing declaration: {keyword} {name}')
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
    print('Registered canonical L4 second-jet completion and cross-family uniqueness')

if __name__ == '__main__':
    main()
