#!/usr/bin/env python3
"""Register exact normalized signed H3 channels and their cofinal consequences."""
from pathlib import Path
import re

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedSignedChannels244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathWeightedGradientNormalizedExcess244',
    'h3PathWeightedInterpolationNormalizedExcess244',
)
THEOREMS = (
    'h3Path_weightedSignedRate_subBaseline_eq_channelSum244',
    'h3Path_weightedRemainder_eq_positiveChannelSum244',
    'h3Path_weightedGradientGap_quotient244',
    'h3Path_weightedInterpolationGap_quotient244',
    'h3Path_weightedGradientThreshold_implies_highExcess244',
    'h3Path_weightedInterpolationThreshold_implies_highExcess244',
    'h3Path_weightedThird_fixedNormalizedCofinal244',
    'h3Path_weightedThird_fixedNormalizedNatSequence244',
    'h3Path_extension_of_boundedNormalizedSignedChannels244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    text = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', text):
        raise SystemExit('Lean proof placeholder detected')
    for kind, names in (('noncomputable def', DEFS), ('theorem', THEOREMS)):
        for name in names:
            if not re.search(r'^' + kind + r'\s+' + re.escape(name) + r'\b',
                             text, re.M):
                raise SystemExit(f'Missing {kind} {name}')

    line = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if line not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [line]) + '\n')

    old_lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys(
        [s for s in old_lines if s.startswith('import ')] + [line]))
    body = [s for s in old_lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in (*DEFS, *THEOREMS):
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for statement in ('#check ' + qualified, '#print axioms ' + qualified):
            if statement not in body:
                body.append(statement)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != AUDIT.read_text():
        AUDIT.write_text(new)
    print('Registered exact normalized signed H3 channel obstruction')

if __name__ == '__main__':
    main()
