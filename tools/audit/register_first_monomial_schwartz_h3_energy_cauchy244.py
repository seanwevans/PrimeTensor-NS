#!/usr/bin/env python3
"""Register H3-energy-to-mixed-jet Cauchy closure for signed Schwartz transport."""
from pathlib import Path

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3SchwartzH3EnergyCauchy244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'SchwartzH3DifferenceEnergyCauchy244'),
    ('theorem', 'schwartzThirdJetDifferenceRoot_sq_le_E3244'),
    ('theorem', 'schwartzSecondJetDifferenceRoot_pow_eight_le_E2E3244'),
    ('theorem', 'SchwartzH3DifferenceEnergyCauchy244.toStrongJets'),
    ('theorem', 'SchwartzH3DifferenceEnergyCauchy244.toMixedGraph'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_existsLimit_of_H3EnergyCauchy244'),
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in src:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [line for line in audit_lines if line.startswith('import ')] + [imp]
    ))
    body = [line for line in audit_lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered H3 energy Cauchy to mixed 81+27 jet graph and signed transport limit')


if __name__ == '__main__':
    main()
