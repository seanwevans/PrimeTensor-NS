#!/usr/bin/env python3
"""Register the reserved-energy sharp lower-transport Schwartz theorems."""
from pathlib import Path
import re

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzReservedEnergy244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullSchwartz_orderwiseBudget_add_reservedMass_le_18_energy244',
    'thirdFullSchwartz_orderwiseBudget_le_18_energy244',
    'h3Path_lowerTransport_abs_add_reservedMass_le_18_energy244',
    'h3Path_deriv_add_fullViscosity_add_reservedMass_le_18_energy244',
    'h3Path_energySlope_pos_of_realSchwartzReservedBudget244',
    'h3Path_highUnabsorbed_realSchwartzReservedAlternative244',
    'h3Path_highUnabsorbed_realSchwartzGradientThreshold244',
    'h3Path_highUnabsorbed_topAdverse_of_realSchwartzGradientCeiling244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', source):
        raise SystemExit('Forbidden placeholder in new proof source')
    actual = set(re.findall(r'^theorem\s+(\w+)', source, re.M))
    missing = set(NAMES) - actual
    if missing:
        raise SystemExit('Missing theorems: '+', '.join(sorted(missing)))
    import_line = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if import_line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [import_line]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys(
        [x for x in lines if x.startswith('import ')] + [import_line]
    ))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        full_name = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in (f'#check {full_name}', f'#print axioms {full_name}'):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(NAMES)} reserved-energy Schwartz theorems')


if __name__ == '__main__':
    main()
