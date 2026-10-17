#!/usr/bin/env python3
"""Register automatic boundedness of Schwartz jet Cauchy approximants."""
from pathlib import Path
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzAutomaticJetBounds244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('theorem', 'schwartzIntegralL2Root_le_add_difference244'),
    ('theorem', 'schwartzIntegralL2Root_sub_comm244'),
    ('theorem', 'schwartzIntegralL2Root_abs_sub_le_difference244'),
    ('theorem', 'Schwartz243StrongJetCauchy244.uniformRoots'),
    ('theorem', 'lowNormalRealSchwartz_firstMonomial_existsLimit_of_strongJetCauchy244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in source:
            raise SystemExit(f'Missing declaration: {name}')
    line = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [line]) + '\n')
    audit_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in audit_lines if line.startswith('import ')] + [line]))
    body = [x for x in audit_lines if not x.startswith('import ')]
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
    print('Registered automatic uniform jet-root bounds and strong-Cauchy monomial limit')

if __name__ == '__main__':
    main()
