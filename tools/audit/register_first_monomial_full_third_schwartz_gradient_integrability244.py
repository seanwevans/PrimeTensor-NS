#!/usr/bin/env python3
"""Idempotently register the real-Schwartz gradient-axis integrability closure."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientIntegrability244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullRealSchwartz_gradientAxisDensity_integrable244',
    'thirdFullRealSchwartz_gradientAxesIntegrable_of_realization244',
    'thirdFullRealSchwartz_pathGradientTotal_eq_of_realization244',
    'h3Path_fullThirdTransport_eq_realSchwartz_of_realization244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if any(token in source for token in ('sorry', 'admit')):
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [imp]
    ))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {q}', f'#print axioms {q}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered full-third Schwartz gradient integrability closure')

if __name__ == '__main__':
    main()
