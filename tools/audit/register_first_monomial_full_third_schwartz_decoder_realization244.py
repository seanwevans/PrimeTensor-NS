#!/usr/bin/env python3
"""Register the real L² decoder to pointwise Schwartz H³ reconstruction bridge."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzDecoderRealization244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('thirdFullSchwartz_zerothRealization_of_decoderEquality244', 'exists_thirdFullSchwartz_exactDecoderApproximation244', 'exists_thirdFullSchwartz_exactDecoderVelocitySequence244', 'thirdFullSchwartz_matchedFirstJetDifference_le_spectralDistance244', 'thirdFullSchwartz_matchedFirstJet_tendsto_canonical244', 'exists_thirdFullSchwartz_velocityFirstJets_tendsto244')


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing {path}')
    content = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', content):
        raise SystemExit('Proof placeholder detected')
    declared = set(re.findall(r'^theorem\s+(\w+)', content, re.M))
    if not set(NAMES) <= declared:
        raise SystemExit('Missing proof declarations')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    orig = AUDIT.read_text()
    xs = orig.splitlines()
    imports = list(dict.fromkeys([x for x in xs if x.startswith('import ')] + [imp]))
    rest = [x for x in xs if not x.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in NAMES:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for statement in (f'#check {fq}', f'#print axioms {fq}'):
            if statement not in rest:
                rest.append(statement)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != orig:
        AUDIT.write_text(updated)
    print(f'Registered {len(NAMES)} decoder-realization theorems')


if __name__ == '__main__':
    main()
