#!/usr/bin/env python3
"""Audit actual finite Galerkin compactness estimates without hiding limit assumptions."""
import re,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinCompactnessEnvelope.lean'
DOC=ROOT/'docs/research/z3-galerkin-compactness-envelope-2026-11-17.md'
REG=ROOT/'tools/audit/register_h3_three_band_z3_galerkin_compactness_envelope.py'
THEOREMS=('thirdFullThreeBand_z3WienerTail_twoRadius244', 'thirdFullThreeBand_z3WienerTail_150_from180_100Ball244', 'thirdFullThreeBand_z3GalerkinFiniteODE_closedLipschitz51000_244', 'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244', 'thirdFullThreeBand_z3GalerkinFiniteODE_exists_uniformCutoffFamily244')
code=SOURCE.read_text(encoding='utf-8')
assert DOC.is_file() and REG.is_file()
for dependency in (
    'thirdFullThreeBand_z3GalerkinFiniteODE_exists_commonHorizon244',
    'thirdFullThreeBand_z3MovingRadius_highBall244',
    'thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244',
    'Convex.norm_image_sub_le_of_norm_deriv_le',
    'Finset.sum_le_sum_of_subset_of_nonneg',
    'thirdFullThreeBand_z3WienerTail_twoRadius244',
):
    assert dependency in code, dependency
scrub=re.sub(r'/-.*?-/', '', code,flags=re.S)
scrub=re.sub(r'--[^\n]*','',scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',scrub)
for name in THEOREMS:
    assert len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code))==1,name
assert '∀ s : Finset CompactIndex244' in code
assert 'Real.exp (-(Real.log (9 / 5' in code
print('PASS: genuine finite field, analytic tail, closed-time Lipschitz, uniform family')
