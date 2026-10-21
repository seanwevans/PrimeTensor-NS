#!/usr/bin/env python3
"""Register exact normalized phase/middle split and physical middle budget."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdGlobalPhaseMiddleCoupling244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathTopFourierGlobalMiddleCouplingNormalizedRate244',
    'h3PathTopFourierGlobalTopPhaseNormalizedRate244',
    'h3PathTopFourierGlobalPhasePenaltyNormalizedRate244',
)
THEOREMS = (
    'h3Path_normalizedExcessRate_eq_middleCoupling_add_topPhase244',
    'h3Path_globalPhasePenaltyNormalizedRate_nonneg244',
    'h3Path_globalTopPhaseRate_eq_phaseFree_add_penalty244',
    'h3Path_globalTopPhaseRate_ge_phaseFree244',
    'h3_middleCoupling_scalar_le_kineticGradientBudget244',
    'h3Path_globalMiddleCoupling_le_kineticGradientBudget244',
    'h3Path_nearYoung_forces_signedTopPhase_after_middleBudget244',
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
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
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
    print(f'Registered {len(DEFS)+len(THEOREMS)} exact middle/phase declarations')

if __name__ == '__main__':
    main()
