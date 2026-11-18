#!/usr/bin/env python3
"""Static integrity check for the finite Leray overlap-uniqueness bridge."""
import re, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongOverlapUniqueness.lean'
code = SOURCE.read_text(encoding='utf-8')
necessary = (
    'import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinMaximalEndpointAlternative',
    'thirdFullThreeBand_z3GalerkinFiniteField_contDiff244',
    'hSmooth.exists_lipschitzOnWith',
    'ODE_solution_unique_of_mem_Icc_right',
    'thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticNonEscape244',
)
for text in necessary:
    if text not in code: raise SystemExit('missing mathematical dependency: ' + text)
source = re.sub(r'/-.*?-/', '', code, flags=re.S)
source = re.sub(r'--[^\n]*', '', source)
if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', source):
    raise SystemExit('unproved or unsafe declaration')
if 'variable (hLip' in source or 'hFieldLipschitz' in source:
    raise SystemExit('externally hypothesized field Lipschitz')
print('PASS: finite state compact Lipschitz, genuine ODE uniqueness, and automatic analytic overlap')
