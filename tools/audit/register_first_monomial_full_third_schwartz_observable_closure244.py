#!/usr/bin/env python3
"""Register full-third Schwartz five-observable sequential closure proofs."""
from pathlib import Path
import re

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzObservableClosure244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'H3FullThirdSchwartzObservableApproximation244',
    'H3FullThirdSchwartzObservableApproximable244',
)
THEOREMS = (
    'h3Path_exactRealSchwartz_implies_fullThirdObservableApproximable244',
    'h3Path_fullThirdObservable_limit_signedEnvelope244',
    'h3Path_fullThirdObservable_limit_spectralDominance244',
    'h3Path_extension_of_fullThirdApproxSignedEnvelope244',
    'h3Path_extension_of_fullThirdApproxSpectralDominance244',
    'h3Path_noExtension_fullThirdApproxSignedWitness244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', src):
        raise SystemExit('Proof placeholder found')
    actual_defs = set(re.findall(r'^def\s+(\w+)', src, re.M))
    actual_theorems = set(re.findall(r'^theorem\s+(\w+)', src, re.M))
    missing = (set(DEFS) - actual_defs) | (set(THEOREMS) - actual_theorems)
    if missing:
        raise SystemExit('Missing declarations: ' + ', '.join(sorted(missing)))
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
    for name in DEFS + THEOREMS:
        fullname = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {fullname}', f'#print axioms {fullname}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(DEFS)} definitions and {len(THEOREMS)} theorems')


if __name__ == '__main__':
    main()
