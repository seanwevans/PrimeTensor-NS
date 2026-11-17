#!/usr/bin/env python3
"""Check source-level provenance and structural obligations of the finite Z3 restart glue."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
FILE = (ROOT / 'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinPreterminalRestartGlue.lean')
source = FILE.read_text(encoding='utf-8')
stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
stripped = re.sub(r'--[^\n]*', '', stripped)
forbidden = re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', stripped)
if forbidden:
    raise SystemExit('Forbidden proof escape: ' + forbidden.group(0))
required = {
    'complete actual Leray preterminal endpoint input':
        'thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticEndpoint244',
    'existing actual finite Picard theorem':
        'thirdFullThreeBand_z3GalerkinFiniteField_exists_local244',
    'approaching sequence derived from topology':
        'mem_closure_iff_seq_limit',
    'preterminal sequence in genuine interval': 'closure_Ico',
    'correct field on left': 'thirdFullThreeBand_z3GalerkinRestartGlue_leftODE244',
    'correct field on right': 'thirdFullThreeBand_z3GalerkinRestartGlue_rightODE244',
    'explicit preterminal endpoint rate': 'hApproach t ht',
    'actual derivative stability under local equality': 'congr_of_eventuallyEq',
    'full research theorem': 'thirdFullThreeBand_z3GalerkinPreterminalGluedRestart244',
}
for label, signature in required.items():
    if signature not in stripped:
        raise SystemExit(f'Missing {label}: {signature}')
if 'thirdFullThreeBandZ3GalerkinNSField244 mu s' in stripped:
    raise SystemExit('Unexpected raw infinite-dimensional state in local restart theorem')
if 'hStrictEnd' in stripped or 'hEndpointStrict' in stripped:
    raise SystemExit('Forbidden new strict endpoint analytic mass hypothesis')
if 'hBall' in stripped or 'hSpeedBound' in stripped:
    raise SystemExit('No postulated post-initial analytic/speed certificate permitted')
if not source.endswith('\n') or any(ln.rstrip() != ln for ln in source.splitlines()):
    raise SystemExit('Lean source formatting error')
print('PASS: actual finite Picard endpoint restart; genuine pasted ODE on both sides')
print('PASS: automatic approaching sequence and no new endpoint strict-ball hypothesis')
print('NOTE: seam derivative and maximal flow remain mathematically open')
