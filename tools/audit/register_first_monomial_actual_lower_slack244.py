#!/usr/bin/env python3
"""Register the exact physical lower-order slack and joint signed rate frontier."""
from pathlib import Path
import re

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdActualLowerOrderSlack244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLARATIONS = (
    ('noncomputable def', 'h3PathActualLowerTransportSlack244'),
    ('theorem', 'h3Path_actualZeroOrderTransport_eq_zero244'),
    ('theorem', 'h3Path_weightedSignedRate_eq_slope_add_lowerSlack244'),
    ('theorem', 'h3Path_actualLowerTransportSlack_bounds244'),
    ('theorem', 'h3Path_signedChannels_sum_eq_physicalGrowth_add_slack244'),
    ('theorem', 'h3Path_effectiveDefect_add_signedChannels_eq_nonlinearBudget_add_slack244'),
    ('theorem', 'h3Path_extension_of_ae_integrable_jointSignedChannel_majorant244'),
    ('theorem', 'h3Path_jointSignedChannel_no_ae_integrable_majorant_on_subtail244'),
)

def main():
    for file in (ROOT, AUDIT, SOURCE):
        if not file.is_file():
            raise SystemExit(f'Missing file: {file}')
    source = SOURCE.read_text(encoding='utf-8')
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for kind, name in DECLARATIONS:
        if not re.search(r'^' + re.escape(kind) + r'\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing {kind} {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text(encoding='utf-8').splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n', encoding='utf-8')
    old = AUDIT.read_text(encoding='utf-8')
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLARATIONS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for line in ('#check ' + fq, '#print axioms ' + fq):
            if line not in body:
                body.append(line)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if old != new:
        AUDIT.write_text(new, encoding='utf-8')
    print('Registered actual H3 lower-order slack and joint signed-channel criterion')

if __name__ == '__main__':
    main()
