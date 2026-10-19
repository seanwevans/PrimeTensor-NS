#!/usr/bin/env python3
"""Register real L2-L2-Linfinity gradient transport continuity."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientL2L2Linf244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('schwartzTripleIntegral_abs_le_L2L2Linf244', 'schwartzIntegralL2Root_tendsto_of_difference244', 'SchwartzGradientTripleL2L2LinfJets244', 'fullGradientTriple_tendsto_of_L2L2LinfJets244', 'SchwartzFullGradientL2L2LinfJets244', 'fullSchwartzGradientTransport_tendsto_of_L2L2LinfJets244', 'H3FullThirdSchwartzNaturalGradientApproximation244', 'H3FullThirdSchwartzNaturalGradientApproximation244.toSplitJet', 'H3FullThirdSchwartzNaturalGradientApproximation244.toObservable', 'H3FullThirdSchwartzNaturalGradientApproximable244', 'h3Path_naturalGradient_implies_observableApproximable244', 'h3Path_noExtension_naturalGradientSignedWitness244', 'h3Path_extension_of_naturalGradientSignedEnvelope244')

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    text = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', text):
        raise SystemExit('Proof placeholder found')
    declared = set(re.findall(r'^(?:theorem|def|structure)\s+([\w.]+)', text, re.M))
    missing = set(NAMES) - declared
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
    for name in NAMES:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {full}', f'#print axioms {full}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(NAMES)} Schwartz L2-L2-Linfinity gradient declarations')

if __name__ == '__main__':
    main()
