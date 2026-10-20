#!/usr/bin/env python3
"""Register the genuinely derived 972-term gradient gauge and H³ completion."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientAutomaticGauge244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'fullGradientTripleSpectralPairEnvelope_le_uniform244',
    'fullSchwartzGradientSpectralPairEnvelope_cauchySmall_of_H3Energy244',
    'exists_fullSchwartzGradientTransport_limit_of_H3Energy244',
    'exists_thirdFullSchwartz_matchedSignedAndGradientLimits244',
)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    src = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', src):
        raise SystemExit('Lean proof placeholder found')
    declared = set(re.findall(r'^theorem\s+(\w+)', src, re.M))
    if not set(NAMES) <= declared:
        raise SystemExit(f'Missing declaration(s): {set(NAMES) - declared}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in ('#check ' + qualified, '#print axioms ' + qualified):
            if check not in body:
                body.append(check)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != old:
        AUDIT.write_text(result)
    print(f'Registered {len(NAMES)} automatic gradient-gauge theorem declarations')


if __name__ == '__main__':
    main()
