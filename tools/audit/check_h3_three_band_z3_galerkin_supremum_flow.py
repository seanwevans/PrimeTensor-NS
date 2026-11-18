#!/usr/bin/env python3
"""Audit the exact finite Galerkin supremum construction and registered claims."""
import re,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinSupremumFlow.lean'
DOC=ROOT/'docs/research/z3-galerkin-supremum-flow-2026-11-17.md'
REG=ROOT/'tools/audit/register_h3_three_band_z3_galerkin_supremum_flow.py'
THEOREMS=('thirdFullThreeBand_z3GalerkinStrongSegment_nonempty244', 'thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244', 'thirdFullThreeBand_z3GalerkinCanonicalUnion_initial244', 'thirdFullThreeBand_z3GalerkinCanonicalUnion_strong244', 'thirdFullThreeBand_z3GalerkinCommonHorizon_gt244', 'thirdFullThreeBand_z3GalerkinCappedEndpoints_nonempty244', 'thirdFullThreeBand_z3GalerkinCappedEndpoints_bddAbove244', 'thirdFullThreeBand_z3GalerkinCappedSup_start_lt244', 'thirdFullThreeBand_z3GalerkinCappedSup_le_horizon244', 'thirdFullThreeBand_z3GalerkinReachable_belowCappedSup244', 'thirdFullThreeBand_z3GalerkinCappedSup_eq_horizon244', 'thirdFullThreeBand_z3GalerkinFiniteODE_exists_commonHorizon244')

code=SOURCE.read_text(encoding='utf-8')
assert DOC.is_file() and REG.is_file()
assert 'thirdFullThreeBand_z3GalerkinFiniteODE_differentEndsAgree244' in code
assert 'thirdFullThreeBand_z3GalerkinPreterminalGluedStrongRestart244' in code
assert 'thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244' in code
assert 'exists_lt_of_lt_csSup' in code and 'le_csSup' in code
assert 'thirdFullThreeBand_z3GalerkinFiniteField_exists_local244' in code
assert 'Classical.choose' in code
assert 'Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)' in code
scrub=re.sub(r'/-.*?-/', '', code,flags=re.S)
scrub=re.sub(r'--[^\n]*','',scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',scrub)
for name in THEOREMS:
    assert len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code))==1,name
print('PASS: canonical segment union, capped supremum contradiction, and closed-horizon construction')
