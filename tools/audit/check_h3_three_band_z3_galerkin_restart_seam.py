#!/usr/bin/env python3
"""Check structural proof obligations for the exact finite Galerkin seam."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
FILE = (ROOT / 'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinRestartSeam.lean')
source = FILE.read_text(encoding='utf-8')
stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
stripped = re.sub(r'--[^\n]*', '', stripped)
forbidden = re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', stripped)
if forbidden:
    raise SystemExit('Forbidden proof escape: ' + forbidden.group(0))
required = {
    'exact finite field': 'thirdFullThreeBandZ3GalerkinFiniteField244',
    'old preterminal ODE': 'thirdFullThreeBand_z3GalerkinRestartGlue_leftODE244',
    'new Picard ODE': 'thirdFullThreeBand_z3GalerkinRestartGlue_rightODE244',
    'automatic endpoint Picard restart': 'thirdFullThreeBand_z3GalerkinPreterminalPicardRestart244',
    'quantitative left endpoint continuity': 'hApproach t',
    'derivative convergence': 'Filter.Tendsto.congr\' hDerivativeEq.symm hFieldLeft',
    'one-sided derivative extension': 'hasDerivWithinAt_Iic_of_tendsto_deriv',
    'right derivative from genuine Picard path': 'hBetaAt.hasDerivWithinAt',
    'joining derivatives': 'hLeft.union hRight',
    'strong ODE at seam': 'thirdFullThreeBand_z3GalerkinRestartGlue_seamHasDerivAt244',
    'strong ODE beyond seam': 'thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244',
    'full half-open interval including seam': 'Ico a (b + delta)',
}
for label, signature in required.items():
    if signature not in stripped:
        raise SystemExit(f'Missing {label}: {signature}')
if 'hStrictEnd' in stripped or 'hEndpointStrict' in stripped:
    raise SystemExit('Forbidden fresh strict endpoint analytic-ball requirement')
if not source.endswith('\n') or any(ln.rstrip() != ln for ln in source.splitlines()):
    raise SystemExit('Lean source formatting error')
print('PASS: actual finite Leray-Galerkin field; matching left/right derivatives at b')
print('PASS: full strong ODE across seam; no postulated endpoint derivative/smallness')
print('NOTE: maximal-solution construction and uniform lifespan are still open')
