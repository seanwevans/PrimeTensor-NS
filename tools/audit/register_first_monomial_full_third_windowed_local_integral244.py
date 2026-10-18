#!/usr/bin/env python3
"""Idempotent registration of full-third window-weighted strict local integral."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdWindowedLocalIntegral244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('thirdFullLabelledWindowedProjectedKernel_continuous244', 'thirdFullLabelledWindowedProjectedKernel_at_centers244', 'thirdFullLabelledWindowedProjectedKernel_exists_negative_local_integral244', 'thirdFullLabelledWindowedProjectedKernel_exists_concrete_negative_integral244')

def main():
    for f in (SOURCE, ROOT, AUDIT):
        if not f.is_file():
            raise SystemExit(f'Missing required file: {f}')
    s = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in s:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in old if line.startswith('import ')] + [imp]))
    body = [line for line in old if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in (f'#check {q}', f'#print axioms {q}'):
            if command not in body:
                body.append(command)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != AUDIT.read_text():
        AUDIT.write_text(new)
    print('Registered full-third labelled windowed local integral')

if __name__ == '__main__':
    main()
