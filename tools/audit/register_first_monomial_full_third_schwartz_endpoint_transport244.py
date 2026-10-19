#!/usr/bin/env python3
"""Register the sharp Schwartz endpoint-transport proof module idempotently."""
from pathlib import Path
import re

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzEndpointTransport244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullSchwartz_energyOrder_arithmeticConvexity244',
    'thirdFullSchwartz_orderwiseBudget_le_endpointMass244',
    'h3Path_lowerTransport_abs_le_realSchwartzEndpointMass244',
    'h3Path_deriv_add_completeSchwartzDissipation_le_endpointMass244',
    'h3Path_energySlope_pos_of_realSchwartzEndpointBudget244',
    'h3Path_highUnabsorbed_realSchwartzEndpointAlternative244',
    'h3Path_highUnabsorbed_topAdverse_of_endpointMassCeiling244',
    'h3Path_noExtension_topAdverseWitness_of_endpointCeiling244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', src):
        raise SystemExit('Proof placeholder found')
    declared = set(re.findall(r'^theorem\s+(\w+)', src, re.M))
    missing = set(NAMES) - declared
    if missing:
        raise SystemExit('Missing theorems: ' + ', '.join(sorted(missing)))
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        fullname = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {fullname}', f'#print axioms {fullname}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(NAMES)} Schwartz endpoint-transport theorems')


if __name__ == '__main__':
    main()
