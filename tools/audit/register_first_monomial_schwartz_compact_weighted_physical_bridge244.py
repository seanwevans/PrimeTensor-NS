#!/usr/bin/env python3
"""Register synchronized weighted H3 / genuine real Schwartz approximation."""
from pathlib import Path
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzCompactWeightedPhysicalBridge244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'exists_h3SmoothCompactWeighted_realSchwartzExact244',
    'exists_h3SmoothCompactWeighted_realSchwartzAndThirdSequence244',
    'exists_h3SmoothCompactWeighted_realSchwartzActualZeroThird244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing expected file: {p}')
    src = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    header = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + q, '#print axioms ' + q):
            if command not in body:
                body.append(command)
    out = '\n'.join(header + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != out:
        AUDIT.write_text(out)
    print('Registered synchronized weighted H3 and real Schwartz physical bridge')

if __name__ == '__main__':
    main()
