#!/usr/bin/env python3
"""Idempotently register the physical-slice uniform first-jet bridge."""
from pathlib import Path
import re

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzPhysicalFirstJet244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'h3PhysicalSnapshotCanonicalSignedMonomial244'),
    ('theorem', 'thirdFullSchwartz_physicalFirstJetError_le_spectral244'),
    ('theorem', 'exists_thirdFullSchwartz_physicalFirstJetGaugeAndSigned244'),
    ('theorem', 'exists_thirdFullSchwartz_physicalFirstJetTendstoAndSigned244'),
)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing {p}')
    source = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', source):
        raise SystemExit('Proof placeholder detected')
    for kind, name in DECLS:
        prefix = r'(?:noncomputable\s+)?def' if kind == 'def' else kind
        if not re.search(r'^' + prefix + r'\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing {kind} {name}')
    import_line = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if import_line not in lines:
        ROOT.write_text('\n'.join(lines + [import_line]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [import_line]))
    body = [l for l in lines if not l.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for line in (f'#check {qualified}', f'#print axioms {qualified}'):
            if line not in body:
                body.append(line)
    rewritten = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if original != rewritten:
        AUDIT.write_text(rewritten)
    print(f'Registered {len(DECLS)} physical first-jet declarations')


if __name__ == '__main__':
    main()
