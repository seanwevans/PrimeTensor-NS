#!/usr/bin/env python3
"""Idempotently register the six-permuted 21-term Fourier derivative symbol."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSixPermutationSymbol244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('noncomputable def', 'thirdFullSixPermutationSymbol244'),
    ('theorem', 'thirdFullSixPermutationSymbol_swap_first244'),
    ('theorem', 'thirdFullSixPermutationSymbol_swap_last244'),
    ('theorem', 'thirdFullOrderedTriadRealSymbol_reflect_frequencies244'),
    ('theorem', 'thirdFullSixPermutationSymbol_reflect_frequencies244'),
    ('theorem', 'thirdFullSixSymbol_solenoidal_triads244'),
    ('theorem', 'thirdFullSixSymbol_each_permutation244'),
    ('theorem', 'thirdFullSixSymbol_nonzero_solenoidal244'),
    ('theorem', 'thirdFullSixSymbol_nonzero244'),
)

def main():
    for f in (SOURCE, ROOT, AUDIT):
        if not f.is_file():
            raise SystemExit(f'Missing required file: {f}')
    source = SOURCE.read_text()
    for head, name in DECLS:
        if f'{head} {name}' not in source:
            raise SystemExit(f'Missing {head} {name}')
    line = f'import {MODULE}'
    root_lines = ROOT.read_text().splitlines()
    if line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [line]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [v for v in audit_lines if v.startswith('import ')] + [line]
    ))
    body = [v for v in audit_lines if not v.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for statement in (f'#check {full}', f'#print axioms {full}'):
            if statement not in body:
                body.append(statement)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered complete six-permuted third-transport derivative symbol')

if __name__ == '__main__':
    main()
