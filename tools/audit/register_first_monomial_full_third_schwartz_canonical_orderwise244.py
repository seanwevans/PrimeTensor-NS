#!/usr/bin/env python3
"""Register the exact Schwartz orderwise transport and high-growth alternative."""
from pathlib import Path

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzCanonicalOrderwise244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'h3Path_exactEnergyBalance_fullThirdSchwartz_noFluxAssumption244',
    'h3Path_lowerTransport_abs_le_realSchwartzOrderwise244',
    'h3Path_deriv_add_completeSchwartzDissipation_le_orderwise244',
    'h3Path_energySlope_pos_of_realSchwartzOrderwiseBudget244',
    'h3Path_realSchwartzOrderwiseNecessary_of_energySlope_pos244',
    'h3Path_highUnabsorbed_realSchwartzOrderwiseAlternative244',
    'h3Path_noExtension_realSchwartzOrderwiseWitness244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    text = SOURCE.read_text()
    import re
    if re.search(r'\b(sorry|admit)\b', text):
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in text:
            raise SystemExit(f'Missing theorem: {name}')
    import_line = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if import_line not in root:
        ROOT.write_text('\n'.join(root + [import_line]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [import_line]
    ))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {qualified}', f'#print axioms {qualified}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print(f'Registered {len(NAMES)} canonical-orderwise real-Schwartz theorems')


if __name__ == '__main__':
    main()
