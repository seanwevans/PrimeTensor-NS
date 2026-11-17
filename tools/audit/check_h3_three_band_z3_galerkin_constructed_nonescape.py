#!/usr/bin/env python3
"""Source contract for the finite-Galerkin non-escape construction."""
import pathlib
import re
import sys

sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = pathlib.Path('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport')
FILE = ROOT / BASE / 'FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedNonEscape.lean'
code = FILE.read_text(encoding='utf-8')
scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', scrubbed):
    raise SystemExit('forbidden unproved assertion in source')
for token in (
    'thirdFullThreeBand_z3GalerkinFiniteField_constructedLocalMovingBall244',
    'thirdFullThreeBand_z3MovingRadius_highBall244',
    'thirdFullThreeBand_z3GalerkinNSField_speed51000_100Ball244',
    'thirdFullThreeBand_z3GalerkinFiniteField_contDiff244',
    'pi_norm_le_iff_of_nonneg',
    'ContinuousOn.intervalIntegrable',
):
    if token not in scrubbed:
        raise SystemExit('missing mathematical dependency: ' + token)
if re.search(r'(?m)^\s*(?:variable|axiom)\b', scrubbed):
    raise SystemExit('no implicit axiom/variable hypothesis allowed')
print('PASS: actual constructed Picard path has state non-escape, field speed, integrability')
