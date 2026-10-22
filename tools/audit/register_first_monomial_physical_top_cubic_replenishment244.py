#!/usr/bin/env python3
"""Register exact physical top cubic/phase surplus and forcing replenishment budget."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopCubicReplenishment244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathPhysicalTopNetCubicPhaseSurplusRate244',
    'h3PathPhysicalTopCubicReplenishmentRate244',
)
THEOREMS = (
    'h3Path_globalFifthMass_nonneg_for_replenishment244',
    'h3Path_topDerivative_add_fifth_add_phase_eq_cubic244',
    'h3Path_topDerivative_le_cubic244',
    'h3Path_positiveTopGrowth_forces_cubic_gt_fifth_add_phase244',
    'h3Path_topPositiveLog_eq_netCubicPhaseSurplus244',
    'h3Path_topPositiveLog_le_cubicReplenishment244',
    'h3Path_topPositiveLog_eq_zero_of_cubic_le_fifth_add_phase244',
    'h3Path_integratedTopReplenishment_le_cubicAction244',
    'h3Path_nearYoung_forces_cubicReplenishmentAction244',
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
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print(f'Registered {len(DEFS) + len(THEOREMS)} physical cubic-replenishment declarations')

if __name__ == '__main__':
    main()
