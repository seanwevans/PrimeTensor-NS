#!/usr/bin/env python3
"""Register the corrected physical six-symbol and Hermitian phase algebra."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalPhaseOrbit244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('noncomputable def', 'thirdFullPhysicalOrderedSymbol244'),
    ('theorem', 'thirdFullPhysicalOrdered_pair_eq_old244'),
    ('noncomputable def', 'thirdFullPhysicalSixSymbol244'),
    ('theorem', 'thirdFullPhysicalSix_eq_prior_six244'),
    ('theorem', 'thirdFullPhysicalSix_reflection244'),
    ('theorem', 'thirdFullPhysicalTriad_solenoidal244'),
    ('theorem', 'thirdFullPhysicalSix_each_corrected244'),
    ('theorem', 'thirdFullPhysicalSix_nonzero244'),
    ('noncomputable def', 'thirdFullPhysicalHermitianOrbit244'),
    ('theorem', 'thirdFullPhysicalHermitianOrbit_eq244'),
    ('theorem', 'thirdFullPhysicalHermitianOrbit_explicit244'),
    ('theorem', 'thirdFullPhysicalHermitianOrbit_physical_phase_nonzero244'),
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for head, name in DECLS:
        if f'{head} {name}' not in source:
            raise SystemExit(f'Missing declaration: {head} {name}')
    if any(word in source for word in ('sorry', 'admit', 'axiom ')):
        # Prose includes the word 'assumptions' but not any of these keywords.
        raise SystemExit('Forbidden proof placeholder or axiom in Lean source')
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
        for stmt in (f'#check {full}', f'#print axioms {full}'):
            if stmt not in body:
                body.append(stmt)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered corrected physical third symbol and Hermitian orbit')


if __name__ == '__main__':
    main()
