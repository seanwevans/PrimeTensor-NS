#!/usr/bin/env python3
"""Register the quantitative homogeneous whole-space Sobolev theorem."""
from pathlib import Path
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3HomogeneousSobolevLimit'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('wholeSpaceC1FDerivL2ToL6_homogeneous_quantitative',)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    text = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in text:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in audit_lines if line.startswith('import ')] + [imp]))
    body = [line for line in audit_lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        full = 'PrimeTensor.Bridge.Euclidean.' + name
        for cmd in ('#check ' + full, '#print axioms ' + full):
            if cmd not in body:
                body.append(cmd)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print('Registered homogeneous whole-space Sobolev limit')

if __name__ == '__main__':
    main()
