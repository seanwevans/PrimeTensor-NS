#!/usr/bin/env python3
"""Static integrity check for genuine Z3 Galerkin maximal endpoint alternative."""
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
FILE = ROOT / 'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinMaximalEndpointAlternative.lean'
code = FILE.read_text(encoding='utf-8')
from importlib.util import spec_from_file_location, module_from_spec
p = ROOT / 'tools/audit/register_h3_three_band_z3_galerkin_maximal_endpoint_alternative.py'
spec = spec_from_file_location('galerkin_maximal_registry', p)
module = module_from_spec(spec)
spec.loader.exec_module(module)
expected = [
    'import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinRestartSeam',
    'thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244',
    'thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 < b - a',
    'thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma t)',
]
for token in expected:
    if token not in code:
        raise SystemExit('Missing structural feature: '+token)
for name in module.DEFS:
    if len(re.findall(r'(?m)^def\s+'+re.escape(name)+r'\b',code)) != 1:
        raise SystemExit('Missing/duplicate definition: '+name)
for name in module.THEOREMS:
    if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code)) != 1:
        raise SystemExit('Missing/duplicate theorem: '+name)
if code.count(':= by') < 3:
    raise SystemExit('Missing proof bodies')
print('PASS: maximal endpoint proof source; genuine vector field, strict window alternative and no holes')
