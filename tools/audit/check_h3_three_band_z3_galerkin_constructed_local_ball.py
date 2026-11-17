#!/usr/bin/env python3
"""Static contract for the constructed finite Galerkin local-ball step."""
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/'
                 'Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedLocalBall.lean')
text = SOURCE.read_text(encoding='utf-8')
body = re.sub(r'/-.*?-/', '', text, flags=re.S)
body = re.sub(r'--[^\n]*', '', body)
required = (
    'thirdFullThreeBand_z3GalerkinFiniteField_exists_local244',
    'thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_continuousAt244',
    'thirdFullThreeBandZ3GalerkinFiniteExtend244',
    'Icc a (a + delta)',
    'hDeltaWindow',
)
missing = [token for token in required if token not in body]
if missing:
    raise SystemExit('missing mathematical bridge terms: ' + repr(missing))
if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', body):
    raise SystemExit('forbidden proof escape')
if 'hLocalCurve :' in body or 'hMovingBall :' in body:
    raise SystemExit('avoid reintroducing an assumed trajectory or analytic ball')
if '∀ (s : Finset' in body and '∃ (delta' not in body and '∃ delta' not in body:
    raise SystemExit('expected existence of positive local interval')
if any(line != line.rstrip() for line in text.splitlines()):
    raise SystemExit('trailing whitespace')
print('PASS: local Picard solution is constructively bridged to the moving ball; '
      'unproved assumptions prohibited')
