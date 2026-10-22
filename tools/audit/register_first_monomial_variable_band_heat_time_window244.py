#!/usr/bin/env python3
"""Register the actual two-band heat-time gap monotonicity and exhaustion bounds."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdVariableBandHeatTimeWindow244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3TwoBandNearYoungHeatRelativeHighMass244',
    'h3TwoBandNearYoungHeatGapAt244',
)
THEOREMS = (
    'h3_twoBandYoungGap_highMass_difference244',
    'h3_twoBandYoungGap_mono_highMass244',
    'h3_twoBandNearYoungHeat_relativeMass_pos_le_one244',
    'h3_twoBandNearYoungHeat_relativeMass_antitone244',
    'h3_twoBandNearYoungHeat_highMass_balance244',
    'h3_twoBandNearYoungHeat_gap_antitone244',
    'h3_twoBandNearYoungHeat_gap_initial244',
    'h3_twoBandNearYoungHeat_gap_nonneg244',
    'h3_twoBandNearYoungHeat_totalGapDrop_le_inverse244',
    'h3_twoBandNearYoungHeat_largeRate_smallTotalChange244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for name in DEFS:
        if not re.search(r'^noncomputable def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {name}')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + fq, '#print axioms ' + fq):
            if command not in body:
                body.append(command)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print(f'Registered {len(DEFS) + len(THEOREMS)} two-band heat-time declarations')

if __name__ == '__main__':
    main()
