#!/usr/bin/env python3
"""Register the strong split-jet Schwartz full-third closure, idempotently."""
from pathlib import Path
import re

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzSplitJetClosure244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullSchwartz_energy_tendsto_of_fourBlocks244',
    'thirdFullSchwartz_dissipation_tendsto_of_fourBlocks244',
    'thirdFullSchwartz_cubic_tendsto_of_splitJets244',
    'H3FullThirdSchwartzSplitJetApproximation244',
    'H3FullThirdSchwartzSplitJetApproximation244.toObservable',
    'H3FullThirdSchwartzSplitJetApproximable244',
    'h3Path_splitJet_implies_fullThirdObservableApproximable244',
    'h3Path_noExtension_splitJetSignedWitness244',
    'h3Path_extension_of_splitJetSignedEnvelope244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Proof placeholder found')
    missing = [name for name in NAMES if name not in source]
    if missing:
        raise SystemExit('Missing declarations: '+', '.join(missing))
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
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {full}', f'#print axioms {full}'):
            if cmd not in body:
                body.append(cmd)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(NAMES)} split-jet declarations')

if __name__ == '__main__':
    main()
